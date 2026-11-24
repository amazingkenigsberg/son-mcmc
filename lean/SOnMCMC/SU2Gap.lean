import SOnMCMC.SU2Spectral

/-!
# Eigenvalues, orthogonality and the `L²` bound on `SU(2)`

Paper: Section 6.4.

* `su2Eig_recurrence`, `su2Eig_mul_sin`: if the trace is `ν`-almost surely `2 cos α`, the
  eigenvalues `λ_k = su2Eig ν k` of a conjugation-invariant walk satisfy the three-term recurrence
  `(k+3) λ_{k+2} = (k+2) (2 cos α) λ_{k+1} - (k+1) λ_k`, hence
  `(k+1) λ_k sin α = sin ((k+1) α)`: the Weyl character formula for `SU(2)`;
* `integral_mul_conj_eq_zero_of_mem_harm`: `harm K ⊥ harm j` in `L²(SU(2))` for `K ≠ j`;
* `su2_l2Bound_of_even`: if `|λ_{2l}| ≤ ρ` for all `l ≥ 1`, the walk contracts every continuous
  even mean-zero function by the factor `ρ` in `L²`;
* `su2_class_l2Bound`: this holds with `ρ = (4c² - 1)/3` for the class measure of `q₀` with
  `c = Re (q₀)₀₀ ≥ √2/2`.
-/

open MeasureTheory Matrix Real
open scoped ComplexConjugate

namespace SOnMCMC

/-! ### Regularity helper -/

theorem memLp_of_continuous_compact {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {F : X → ℂ}
    (hF : Continuous F) : MemLp F 2 μ := by
  obtain ⟨C, hC⟩ := (isCompact_range hF).isBounded.exists_norm_le
  exact MemLp.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC _ ⟨x, rfl⟩)

/-! ### The trace identity and the three-term recurrence -/

/-- For a conjugation-invariant probability measure, `∫ F dν = λ_k F(1)` for `F ∈ harm k`. -/
theorem integral_of_mem_harm (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    {k : ℕ} {F : SU2 → ℂ} (hF : F ∈ harm k) : ∫ q, F q ∂ν = su2Eig ν k * F 1 := by
  have h := congrFun (markovOp_of_mem_harm ν hν hF) 1
  simpa [markovOp] using h

/-- **The trace identity.** -/
theorem su2Eig_trace_identity (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    (k : ℕ) :
    ((k : ℂ) + 2) * ∫ q : SU2, (q.1 0 0 + q.1 1 1) * q.1 0 0 ^ (k + 1) ∂ν
      = ((k : ℂ) + 3) * su2Eig ν (k + 2) + ((k : ℂ) + 1) * su2Eig ν k := by
  have hG := polar_two (Pi.single 0 1) (Pi.single 1 1) (Pi.single 0 1) (Pi.single 1 1) k
  have h1 := integral_of_mem_harm ν hν hG
  have hpt : ∀ q : SU2,
      (((k + 1 : ℕ) : ℂ) • (lin (Pi.single 0 1) (Pi.single 0 1) ^ k
          * lin (Pi.single 0 1) (Pi.single 1 1) * lin (Pi.single 1 1) (Pi.single 0 1))
        + lin (Pi.single 0 1) (Pi.single 0 1) ^ (k + 1) * lin (Pi.single 1 1) (Pi.single 1 1)) q
      = ((k : ℂ) + 2) * (q.1 0 0 ^ (k + 1) * q.1 1 1) - ((k : ℂ) + 1) * q.1 0 0 ^ k := by
    intro q
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul, lin_single]
    push_cast
    linear_combination (-((k : ℂ) + 1) * q.1 0 0 ^ k) * SU2.det_eq q
  have hc00 := continuous_coord 0 0
  have hc11 := continuous_coord 1 1
  have hint1 : Integrable (fun q : SU2 => q.1 0 0 ^ (k + 1) * q.1 1 1) ν :=
    integrable_of_continuous_su2 ν ((hc00.pow _).mul hc11)
  have hint2 : Integrable (fun q : SU2 => q.1 0 0 ^ k) ν :=
    integrable_of_continuous_su2 ν (hc00.pow _)
  have hint3 : Integrable (fun q : SU2 => q.1 0 0 ^ (k + 2)) ν :=
    integrable_of_continuous_su2 ν (hc00.pow _)
  have h2 : ((k : ℂ) + 2) * ∫ q : SU2, q.1 0 0 ^ (k + 1) * q.1 1 1 ∂ν
      - ((k : ℂ) + 1) * su2Eig ν k = su2Eig ν (k + 2) := by
    rw [hpt 1, SU2.coe_one] at h1
    simp only [hpt] at h1
    rw [integral_sub (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul] at h1
    simp only [Matrix.one_apply_eq, one_pow, mul_one] at h1
    rw [su2Eig]
    linear_combination h1
  have h4 : ∫ q : SU2, (q.1 0 0 + q.1 1 1) * q.1 0 0 ^ (k + 1) ∂ν
      = su2Eig ν (k + 2) + ∫ q : SU2, q.1 0 0 ^ (k + 1) * q.1 1 1 ∂ν := by
    have : ∀ q : SU2, (q.1 0 0 + q.1 1 1) * q.1 0 0 ^ (k + 1)
        = q.1 0 0 ^ (k + 2) + q.1 0 0 ^ (k + 1) * q.1 1 1 := fun q => by ring
    simp only [this]
    rw [integral_add hint3 hint1, su2Eig]
  rw [h4]
  linear_combination h2

/-- The element `!![0, 1; -1, 0]` of `SU(2)`. -/
def wEl : SU2 := SU2.mk' 0 1 (by simp)

theorem wEl_conj_00 (q : SU2) :
    ((wEl * q * wEl⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = q.1 1 1 := by
  rw [SU2.coe_mul, SU2.coe_mul, SU2.coe_inv, wEl, SU2.mk'_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two, star_apply, vecMul, dotProduct]

theorem two_mul_su2Eig_one (ν : Measure SU2) [IsFiniteMeasure ν] (hν : IsConjInvariant ν) :
    2 * su2Eig ν 1 = ∫ q : SU2, (q.1 0 0 + q.1 1 1) ∂ν := by
  have h := integral_conj_eq ν hν wEl (continuous_coord 0 0)
  simp only [wEl_conj_00] at h
  rw [integral_add (integrable_of_continuous_su2 ν (continuous_coord 0 0))
    (integrable_of_continuous_su2 ν (continuous_coord 1 1)), h, su2Eig]
  simp only [pow_one]
  ring

/-- **Three-term recurrence.** If the trace is `ν`-almost surely `c`, then
`(k+3) λ_{k+2} = (k+2) c λ_{k+1} - (k+1) λ_k`. -/
theorem su2Eig_recurrence (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    {c : ℂ} (hc : ∀ᵐ q : SU2 ∂ν, q.1 0 0 + q.1 1 1 = c) (k : ℕ) :
    ((k : ℂ) + 3) * su2Eig ν (k + 2)
      = ((k : ℂ) + 2) * c * su2Eig ν (k + 1) - ((k : ℂ) + 1) * su2Eig ν k := by
  have h := su2Eig_trace_identity ν hν k
  have h2 : ∫ q : SU2, (q.1 0 0 + q.1 1 1) * q.1 0 0 ^ (k + 1) ∂ν = c * su2Eig ν (k + 1) := by
    rw [su2Eig, ← integral_const_mul]
    refine integral_congr_ae (hc.mono fun q hq => ?_)
    show (q.1 0 0 + q.1 1 1) * q.1 0 0 ^ (k + 1) = c * q.1 0 0 ^ (k + 1)
    rw [hq]
  rw [h2] at h
  linear_combination (-1 : ℂ) * h

/-- `S_k(α) = sin ((k+1) α)`. -/
noncomputable def chebS (α : ℝ) (k : ℕ) : ℝ := sin ((k + 1 : ℕ) * α)

theorem chebS_zero (α : ℝ) : chebS α 0 = sin α := by simp [chebS]

theorem chebS_one (α : ℝ) : chebS α 1 = 2 * cos α * sin α := by
  have : ((1 + 1 : ℕ) : ℝ) * α = 2 * α := by norm_num
  rw [chebS, this, sin_two_mul]
  ring

theorem chebS_add_two (α : ℝ) (k : ℕ) :
    chebS α (k + 2) = 2 * cos α * chebS α (k + 1) - chebS α k := by
  simp only [chebS]
  have h1 : ((k + 2 + 1 : ℕ) : ℝ) * α = ((k + 1 + 1 : ℕ) : ℝ) * α + α := by
    push_cast
    ring
  have h2 : ((k + 1 : ℕ) : ℝ) * α = ((k + 1 + 1 : ℕ) : ℝ) * α - α := by
    push_cast
    ring
  rw [h1, h2, sin_add, sin_sub]
  ring

/-- **The Weyl character formula for `SU(2)`.** If the trace is `ν`-almost surely `2 cos α`,
then `(k+1) λ_k sin α = sin ((k+1) α)`. -/
theorem su2Eig_mul_sin (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    {α : ℝ} (hc : ∀ᵐ q : SU2 ∂ν, q.1 0 0 + q.1 1 1 = ((2 * cos α : ℝ) : ℂ)) (k : ℕ) :
    ((k : ℂ) + 1) * su2Eig ν k * ((sin α : ℝ) : ℂ) = ((chebS α k : ℝ) : ℂ) := by
  have h0 : (((0 : ℕ) : ℂ) + 1) * su2Eig ν 0 * ((sin α : ℝ) : ℂ) = ((chebS α 0 : ℝ) : ℂ) := by
    rw [su2Eig_zero, chebS_zero]
    simp
  have h1 : (((1 : ℕ) : ℂ) + 1) * su2Eig ν 1 * ((sin α : ℝ) : ℂ) = ((chebS α 1 : ℝ) : ℂ) := by
    have e1 := two_mul_su2Eig_one ν hν
    have e2 : ∫ q : SU2, (q.1 0 0 + q.1 1 1) ∂ν = ((2 * cos α : ℝ) : ℂ) := by
      rw [integral_congr_ae hc]
      simp
    rw [e2] at e1
    rw [chebS_one]
    push_cast
    push_cast at e1
    linear_combination (Complex.sin (α : ℂ)) * e1
  have hstep : ∀ k : ℕ,
      ((k : ℂ) + 1) * su2Eig ν k * ((sin α : ℝ) : ℂ) = ((chebS α k : ℝ) : ℂ) →
      (((k + 1 : ℕ) : ℂ) + 1) * su2Eig ν (k + 1) * ((sin α : ℝ) : ℂ)
        = ((chebS α (k + 1) : ℝ) : ℂ) →
      (((k + 2 : ℕ) : ℂ) + 1) * su2Eig ν (k + 2) * ((sin α : ℝ) : ℂ)
        = ((chebS α (k + 2) : ℝ) : ℂ) := by
    intro k ih0 ih1
    have hrec := su2Eig_recurrence ν hν hc k
    rw [chebS_add_two]
    push_cast
    push_cast at ih0 ih1 hrec
    linear_combination (Complex.sin (α : ℂ)) * hrec + (2 * Complex.cos (α : ℂ)) * ih1 - ih0
  have key : ∀ k : ℕ,
      (((k : ℂ) + 1) * su2Eig ν k * ((sin α : ℝ) : ℂ) = ((chebS α k : ℝ) : ℂ)) ∧
      ((((k + 1 : ℕ) : ℂ) + 1) * su2Eig ν (k + 1) * ((sin α : ℝ) : ℂ)
        = ((chebS α (k + 1) : ℝ) : ℂ)) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih => exact ⟨ih.2, hstep k ih.1 ih.2⟩
  exact (key k).1

/-! ### Class measures -/

/-- The trace is constant on a conjugacy class. -/
theorem ae_classMeasure_trace (q₀ : SU2) :
    ∀ᵐ q : SU2 ∂(classMeasure haarSU2 q₀), q.1 0 0 + q.1 1 1 = q₀.1 0 0 + q₀.1 1 1 := by
  have hmeas : MeasurableSet {q : SU2 | q.1 0 0 + q.1 1 1 = q₀.1 0 0 + q₀.1 1 1} :=
    (isClosed_eq ((continuous_coord 0 0).add (continuous_coord 1 1))
      continuous_const).measurableSet
  rw [classMeasure, ae_map_iff (measurable_conj_left q₀).aemeasurable hmeas]
  refine Filter.Eventually.of_forall fun g => ?_
  have hsg : star g.1 * g.1 = 1 := mem_unitaryGroup_iff'.mp (SU2.coe_mem_unitary g)
  rw [← Matrix.trace_fin_two, ← Matrix.trace_fin_two, SU2.coe_mul, SU2.coe_mul, SU2.coe_inv,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, hsg, Matrix.one_mul]

theorem norm_su2Eig_le_one (ν : Measure SU2) [IsProbabilityMeasure ν] (k : ℕ) :
    ‖su2Eig ν k‖ ≤ 1 := by
  have h : ∀ q : SU2, ‖q.1 0 0 ^ k‖ ≤ 1 := by
    intro q
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (entry_norm_bound_of_unitary (SU2.coe_mem_unitary q) 0 0)
  have := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall h)
  simpa [su2Eig] using this

/-- **Eigenvalues of a class measure.** For `q₀` with `c = Re (q₀)₀₀ ≥ √2/2`, the even
eigenvalues are dominated by `λ₂ = (4c² - 1)/3`. -/
theorem norm_su2Eig_class_le (q₀ : SU2) (hc0 : 0 ≤ (q₀.1 0 0).re)
    (hc1 : 1 ≤ 2 * (q₀.1 0 0).re ^ 2) {l : ℕ} (hl : 1 ≤ l) :
    ‖su2Eig (classMeasure haarSU2 q₀) (2 * l)‖ ≤ (4 * (q₀.1 0 0).re ^ 2 - 1) / 3 := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (q₀.1 0 0).re := ⟨_, rfl⟩
  rw [← hcdef] at hc0 hc1 ⊢
  have hcle : c ≤ 1 := by
    rw [hcdef]
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans
      (entry_norm_bound_of_unitary (SU2.coe_mem_unitary q₀) 0 0))
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = arccos c := ⟨_, rfl⟩
  have hcos : cos α = c := by
    rw [hα]
    exact cos_arccos (by linarith) hcle
  have hα0 : 0 ≤ α := by
    rw [hα]
    exact arccos_nonneg c
  have hsqrt : √2 / 2 ≤ c := by
    by_contra h
    push Not at h
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hα1 : α ≤ π / 4 := by
    have h1 : arccos c ≤ arccos (√2 / 2) := arccos_le_arccos hsqrt
    rw [← cos_pi_div_four, arccos_cos (by positivity) (by linarith [pi_pos])] at h1
    rw [hα]
    exact h1
  have hinv : IsConjInvariant (classMeasure haarSU2 q₀) := classMeasure_isConjInvariant haarSU2 q₀
  have htr : ∀ᵐ q : SU2 ∂(classMeasure haarSU2 q₀),
      q.1 0 0 + q.1 1 1 = ((2 * cos α : ℝ) : ℂ) := by
    filter_upwards [ae_classMeasure_trace q₀] with q hq
    rw [hq, SU2.coe_11, Complex.add_conj, hcos, hcdef]
  have hsin := su2Eig_mul_sin _ hinv htr (2 * l)
  have hrho : (4 * c ^ 2 - 1) / 3 = so3CharRatio 1 (2 * α) := by
    rw [so3CharRatio_one_eq, cos_two_mul, hcos]
    ring
  rw [hrho]
  refine le_trans ?_ (abs_so3CharRatio_le hl (by linarith) (by linarith))
  have hhalf : 2 * α / 2 = α := by ring
  by_cases hs : sin α = 0
  · have h1 : so3CharRatio l (2 * α) = 1 := by simp [so3CharRatio, hhalf, hs]
    rw [h1, abs_one]
    exact norm_su2Eig_le_one _ _
  · have hval : so3CharRatio l (2 * α)
        = sin ((2 * l + 1 : ℕ) * α) / ((2 * l + 1 : ℕ) * sin α) := by
      simp [so3CharRatio, hhalf, hs]
    have hlam : su2Eig (classMeasure haarSU2 q₀) (2 * l)
        = ((so3CharRatio l (2 * α) : ℝ) : ℂ) := by
      rw [hval]
      have hsC : Complex.sin (α : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_sin]
        exact_mod_cast hs
      have hmC : (2 * (l : ℂ) + 1) ≠ 0 := by
        have h2 : ((2 * l + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast at h2
        exact h2
      rw [chebS] at hsin
      push_cast
      push_cast at hsin
      rw [eq_div_iff (mul_ne_zero hmC hsC)]
      linear_combination hsin
    rw [hlam, Complex.norm_real, Real.norm_eq_abs]

/-! ### Orthogonality -/

theorem wEl_torus (φ : ℝ) : wEl * torus φ * wEl⁻¹ = (torus φ)⁻¹ := by
  apply Subtype.ext
  rw [SU2.coe_mul, SU2.coe_mul, SU2.coe_inv, SU2.coe_inv, torus_coe, wEl, SU2.mk'_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, star_apply, ← Complex.exp_conj]

theorem torus_trace (φ : ℝ) :
    (torus φ).1 0 0 + (torus φ).1 1 1 = ((2 * cos φ : ℝ) : ℂ) := by
  rw [torus_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  push_cast
  rw [Complex.two_cos, neg_mul]

theorem integral_mul_conj_eq_zero_of_lt {K j : ℕ} (hjK : j < K) {F H : SU2 → ℂ}
    (hF : F ∈ harm K) (hH : H ∈ harm j) : ∫ x, F x * conj (H x) ∂haarSU2 = 0 := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = π / (K + 1) := ⟨_, rfl⟩
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hK2 : (2 : ℝ) ≤ (K : ℝ) + 1 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    linarith
  have hα0 : 0 < α := by
    rw [hα]
    exact div_pos pi_pos hK1
  have hαπ : α < π := by
    rw [hα, div_lt_iff₀ hK1]
    nlinarith [pi_pos]
  have hKα : ((K + 1 : ℕ) : ℝ) * α = π := by
    rw [hα]
    push_cast
    field_simp
  have hinv : IsConjInvariant (classMeasure haarSU2 (torus α)) :=
    classMeasure_isConjInvariant haarSU2 (torus α)
  have hsymm : (classMeasure haarSU2 (torus α)).IsInvInvariant :=
    ⟨classMeasure_map_inv haarSU2 (wEl_torus α)⟩
  have htr : ∀ᵐ q : SU2 ∂(classMeasure haarSU2 (torus α)),
      q.1 0 0 + q.1 1 1 = ((2 * cos α : ℝ) : ℂ) := by
    filter_upwards [ae_classMeasure_trace (torus α)] with q hq
    rw [hq, torus_trace]
  have hsinα : sin α ≠ 0 := (sin_pos_of_pos_of_lt_pi hα0 hαπ).ne'
  have h2 : ((sin α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsinα
  -- `λ_K = 0`
  have hlamK : su2Eig (classMeasure haarSU2 (torus α)) K = 0 := by
    have h := su2Eig_mul_sin _ hinv htr K
    rw [chebS, hKα, sin_pi, Complex.ofReal_zero] at h
    have h1 : ((K : ℂ) + 1) ≠ 0 := by exact_mod_cast hK1.ne'
    rcases mul_eq_zero.mp h with h3 | h3
    · exact (mul_eq_zero.mp h3).resolve_left h1
    · exact absurd h3 h2
  -- `λ_j ≠ 0`
  have hlamj : su2Eig (classMeasure haarSU2 (torus α)) j ≠ 0 := by
    intro h0
    have h := su2Eig_mul_sin _ hinv htr j
    rw [h0, mul_zero, zero_mul] at h
    have hpos : 0 < chebS α j := by
      rw [chebS]
      refine sin_pos_of_pos_of_lt_pi (mul_pos (by positivity) hα0) ?_
      rw [← hKα]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.succ_lt_succ hjK) hα0
    have h3 : chebS α j = 0 := by exact_mod_cast h.symm
    linarith
  have hFc := continuous_of_mem_harm hF
  have hHc' : (fun x => conj (H x)) ∈ harm j := conj_mem_harm hH
  have hHc := continuous_of_mem_harm hHc'
  have hsa := integral_markovOp_mul haarSU2 (classMeasure haarSU2 (torus α))
    (memLp_of_continuous_compact haarSU2 hFc) (memLp_of_continuous_compact haarSU2 hHc)
  rw [markovOp_of_mem_harm _ hinv hF, markovOp_of_mem_harm _ hinv hHc', hlamK] at hsa
  simp only [zero_mul, integral_zero, Pi.smul_apply, smul_eq_mul] at hsa
  have h3 : ∫ x, F x * (su2Eig (classMeasure haarSU2 (torus α)) j * conj (H x)) ∂haarSU2
      = su2Eig (classMeasure haarSU2 (torus α)) j * ∫ x, F x * conj (H x) ∂haarSU2 := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [h3] at hsa
  exact (mul_eq_zero.mp hsa.symm).resolve_left hlamj

/-- **Orthogonality.** The spaces `harm K` are pairwise orthogonal in `L²(SU(2))`. -/
theorem integral_mul_conj_eq_zero_of_mem_harm {K j : ℕ} (hKj : K ≠ j) {F H : SU2 → ℂ}
    (hF : F ∈ harm K) (hH : H ∈ harm j) : ∫ x, F x * conj (H x) ∂haarSU2 = 0 := by
  rcases Nat.lt_or_gt_of_ne hKj with h | h
  · have h1 := integral_mul_conj_eq_zero_of_lt h hH hF
    have h2 : ∫ x, F x * conj (H x) ∂haarSU2 = conj (∫ x, H x * conj (F x) ∂haarSU2) := by
      rw [← integral_conj]
      congr 1
      funext x
      simp [mul_comm]
    rw [h2, h1, map_zero]
  · exact integral_mul_conj_eq_zero_of_lt h hF hH

theorem exists_const_of_mem_harm_zero {F : SU2 → ℂ} (hF : F ∈ harm 0) :
    ∃ a : ℂ, F = fun _ => a := by
  refine Submodule.span_induction (p := fun F _ => ∃ a : ℂ, F = fun _ => a) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨⟨u, v⟩, rfl⟩
    exact ⟨1, by funext x; simp⟩
  · exact ⟨0, rfl⟩
  · rintro a b _ _ ⟨a', rfl⟩ ⟨b', rfl⟩
    exact ⟨a' + b', rfl⟩
  · rintro c a _ ⟨a', rfl⟩
    exact ⟨c * a', rfl⟩

theorem integral_eq_zero_of_mem_harm {k : ℕ} (hk : k ≠ 0) {F : SU2 → ℂ} (hF : F ∈ harm k) :
    ∫ x, F x ∂haarSU2 = 0 := by
  have h := integral_mul_conj_eq_zero_of_mem_harm hk hF (lin_pow_mem 0 0 0)
  simpa using h

/-! ### The `L²` bound -/

theorem markovOp_sum_harm (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    (S : Finset ℕ) (f : ℕ → SU2 → ℂ) (hf : ∀ k ∈ S, f k ∈ harm k) :
    markovOp ν (fun x => ∑ k ∈ S, f k x) = fun x => ∑ k ∈ S, su2Eig ν k * f k x := by
  funext x
  have hint : ∀ k ∈ S, Integrable (fun g => f k (x * g)) ν := fun k hk =>
    integrable_of_continuous_su2 ν
      ((continuous_of_mem_harm (hf k hk)).comp (continuous_const.mul continuous_id))
  simp only [markovOp]
  rw [integral_finsetSum S hint]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := congrFun (markovOp_of_mem_harm ν hν (hf k hk)) x
  simpa [markovOp] using this

/-- **Pythagoras for the walk.** On a finite sum of eigenfunctions with eigenvalues bounded by
`ρ`, the walk contracts the `L²` norm by `ρ`. -/
theorem integral_norm_sq_markovOp_sum_harm (ν : Measure SU2) [IsProbabilityMeasure ν]
    (hν : IsConjInvariant ν) (S : Finset ℕ) (f : ℕ → SU2 → ℂ) (hf : ∀ k ∈ S, f k ∈ harm k)
    {ρ : ℝ} (hρ : ∀ k ∈ S, ‖su2Eig ν k‖ ≤ ρ) :
    ∫ x, ‖markovOp ν (fun x => ∑ k ∈ S, f k x) x‖ ^ 2 ∂haarSU2
      ≤ ρ ^ 2 * ∫ x, ‖∑ k ∈ S, f k x‖ ^ 2 ∂haarSU2 := by
  have hint : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun x => f i x * conj (f j x)) haarSU2 :=
    fun i hi j hj => integrable_of_continuous_su2 _
      ((continuous_of_mem_harm (hf i hi)).mul (continuous_of_mem_harm (conj_mem_harm (hf j hj))))
  have horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∫ x, f i x * conj (f j x) ∂haarSU2 = 0 :=
    fun i hi j hj hij => integral_mul_conj_eq_zero_of_mem_harm hij (hf i hi) (hf j hj)
  have h1 := integral_norm_sq_sum_of_orthogonal haarSU2 S f (fun k => su2Eig ν k) hint horth
  have h2 := integral_norm_sq_sum_of_orthogonal haarSU2 S f (fun _ => 1) hint horth
  simp only [one_mul, norm_one, one_pow] at h2
  rw [markovOp_sum_harm ν hν S f hf]
  beta_reduce
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have h3 : ‖su2Eig ν k‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hρ k hk) 2
  exact mul_le_mul_of_nonneg_right h3 (integral_nonneg fun x => by positivity)

/-- A continuous even mean-zero function on `SU(2)` is uniformly approximated by finite sums of
elements of `harm (2l)`, `l ≥ 1`. -/
theorem exists_even_harm_near {F : SU2 → ℂ} (hFc : Continuous F)
    (heven : ∀ x, F (negOne * x) = F x) (hmean : ∫ x, F x ∂haarSU2 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset ℕ) (f : ℕ → SU2 → ℂ), (∀ k ∈ S, f k ∈ harm k) ∧
      (∀ k ∈ S, ∃ l, 1 ≤ l ∧ k = 2 * l) ∧ ∀ x, ‖F x - ∑ k ∈ S, f k x‖ ≤ 2 * ε := by
  obtain ⟨h, hh, hnear⟩ := exists_harmAll_near ⟨F, hFc⟩ hε
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp harm h).mp hh
  have hhx : ∀ x, h x = ∑ k ∈ f.support, f k x := by
    intro x
    rw [← hsum, Finsupp.sum, Finset.sum_apply]
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = f.support.filter (fun k => Even k) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = T.erase 0 := ⟨_, rfl⟩
  -- the even part of `h`
  have hE : ∀ x, ∑ k ∈ T, f k x = (h x + h (negOne * x)) / 2 := by
    intro x
    rw [hhx, hhx, hT, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [harm_parity (hf k) x]
    split_ifs with hk
    · rw [hk.neg_one_pow]
      ring
    · rw [(Nat.not_even_iff_odd.mp hk).neg_one_pow]
      ring
  have hEnear : ∀ x, ‖F x - ∑ k ∈ T, f k x‖ ≤ ε := by
    intro x
    rw [hE]
    have h1 := hnear x
    have h2 := hnear (negOne * x)
    simp only [ContinuousMap.coe_mk] at h1 h2
    rw [heven] at h2
    have e : F x - (h x + h (negOne * x)) / 2
        = ((F x - h x) + (F x - h (negOne * x))) / 2 := by ring
    rw [e, norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
    linarith [norm_add_le (F x - h x) (F x - h (negOne * x))]
  -- the constant term
  obtain ⟨a, ha⟩ := exists_const_of_mem_harm_zero (hf 0)
  have hTS : ∀ x, ∑ k ∈ T, f k x = ∑ k ∈ S, f k x + a := by
    intro x
    by_cases h0 : 0 ∈ T
    · rw [hS, ← Finset.sum_erase_add _ _ h0, show f 0 x = a from congrFun ha x]
    · have hf0 : f 0 = 0 := by
        by_contra hne
        apply h0
        rw [hT, Finset.mem_filter]
        exact ⟨Finsupp.mem_support_iff.mpr hne, Even.zero⟩
      have ha0 : a = 0 := by
        have := congrFun ha 1
        rw [hf0] at this
        simpa using this.symm
      rw [hS, Finset.erase_eq_of_notMem h0, ha0, add_zero]
  have hint : ∀ k, Integrable (f k) haarSU2 := fun k =>
    integrable_of_continuous_su2 _ (continuous_of_mem_harm (hf k))
  have hSmem : ∀ k ∈ S, Even k ∧ k ≠ 0 := by
    intro k hk
    rw [hS, Finset.mem_erase, hT, Finset.mem_filter] at hk
    exact ⟨hk.2.2, hk.1⟩
  have hSint : ∫ x, ∑ k ∈ S, f k x ∂haarSU2 = 0 := by
    rw [integral_finsetSum S fun k _ => hint k]
    exact Finset.sum_eq_zero fun k hk => integral_eq_zero_of_mem_harm (hSmem k hk).2 (hf k)
  have hTint : ∫ x, ∑ k ∈ T, f k x ∂haarSU2 = a := by
    simp only [hTS]
    rw [integral_add (integrable_finsetSum S fun k _ => hint k) (integrable_const a), hSint,
      zero_add]
    simp
  have hEcont : Continuous fun x => ∑ k ∈ T, f k x :=
    continuous_finsetSum T fun k _ => continuous_of_mem_harm (hf k)
  have ha_le : ‖a‖ ≤ ε := by
    have h1 : ∫ x, (∑ k ∈ T, f k x - F x) ∂haarSU2 = a := by
      rw [integral_sub (integrable_of_continuous_su2 _ hEcont)
        (integrable_of_continuous_su2 _ hFc), hTint, hmean, sub_zero]
    rw [← h1]
    have h2 := norm_integral_le_of_norm_le_const (μ := haarSU2)
      (f := fun x => ∑ k ∈ T, f k x - F x) (C := ε)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_sub_rev]
        exact hEnear x)
    simpa using h2
  refine ⟨S, f, fun k _ => hf k, ?_, fun x => ?_⟩
  · intro k hk
    obtain ⟨hev, hne⟩ := hSmem k hk
    obtain ⟨l, hl⟩ := hev
    exact ⟨l, by omega, by omega⟩
  · have h1 := hEnear x
    rw [hTS] at h1
    have e : F x - ∑ k ∈ S, f k x = (F x - (∑ k ∈ S, f k x + a)) + a := by ring
    rw [e]
    linarith [norm_add_le (F x - (∑ k ∈ S, f k x + a)) a]

/-- **`L²` bound from the even eigenvalues.** If `|λ_{2l}(ν)| ≤ ρ` for all `l ≥ 1`, the walk
contracts every continuous even mean-zero function on `SU(2)` by the factor `ρ`. -/
theorem su2_l2Bound_of_even (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    {ρ : ℝ} (hρ : ∀ l : ℕ, 1 ≤ l → ‖su2Eig ν (2 * l)‖ ≤ ρ) {F : SU2 → ℂ} (hFc : Continuous F)
    (heven : ∀ x, F (negOne * x) = F x) (hmean : ∫ x, F x ∂haarSU2 = 0) :
    ∫ x, ‖markovOp ν F x‖ ^ 2 ∂haarSU2 ≤ ρ ^ 2 * ∫ x, ‖F x‖ ^ 2 ∂haarSU2 := by
  refine integral_norm_sq_markovOp_le_of_approx haarSU2 ν (memLp_of_continuous_compact _ hFc)
    fun ε hε => ?_
  obtain ⟨S, f, hf, hS, hnear⟩ :=
    exists_even_harm_near hFc heven hmean (ε := √ε / 2) (by positivity)
  refine ⟨fun x => ∑ k ∈ S, f k x, memLp_of_continuous_compact _
    (continuous_finsetSum S fun k hk => continuous_of_mem_harm (hf k hk)), ?_, ?_⟩
  · have h1 : ∀ x, ‖F x - ∑ k ∈ S, f k x‖ ^ 2 ≤ ε := by
      intro x
      have h2 := hnear x
      have h3 : 2 * (√ε / 2) = √ε := by ring
      rw [h3] at h2
      calc ‖F x - ∑ k ∈ S, f k x‖ ^ 2 ≤ √ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = ε := Real.sq_sqrt hε.le
    have h4 := integral_mono_of_nonneg (μ := haarSU2)
      (Filter.Eventually.of_forall fun x => by positivity) (integrable_const ε)
      (Filter.Eventually.of_forall h1)
    simpa using h4
  · exact integral_norm_sq_markovOp_sum_harm ν hν S f hf fun k hk => by
      obtain ⟨l, hl, rfl⟩ := hS k hk
      exact hρ l hl

/-- **The `L²` bound for a conjugacy class of `SU(2)`.** For `q₀` with `c = Re (q₀)₀₀ ≥ √2/2`,
the walk whose steps are uniform on the conjugacy class of `q₀` contracts continuous even
mean-zero functions by the factor `(4c² - 1)/3`. -/
theorem su2_class_l2Bound (q₀ : SU2) (hc0 : 0 ≤ (q₀.1 0 0).re)
    (hc1 : 1 ≤ 2 * (q₀.1 0 0).re ^ 2) {F : SU2 → ℂ} (hFc : Continuous F)
    (heven : ∀ x, F (negOne * x) = F x) (hmean : ∫ x, F x ∂haarSU2 = 0) :
    ∫ x, ‖markovOp (classMeasure haarSU2 q₀) F x‖ ^ 2 ∂haarSU2
      ≤ ((4 * (q₀.1 0 0).re ^ 2 - 1) / 3) ^ 2 * ∫ x, ‖F x‖ ^ 2 ∂haarSU2 :=
  su2_l2Bound_of_even _ (classMeasure_isConjInvariant haarSU2 q₀)
    (fun _ hl => norm_su2Eig_class_le q₀ hc0 hc1 hl) hFc heven hmean

end SOnMCMC

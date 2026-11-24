import SOnMCMC.ClassMeasure
import SOnMCMC.SU2Harmonic
import SOnMCMC.SO3

/-!
# Spectral theory of conjugation-invariant walks on `SU(2)`

Paper: Section 6.4.

* `markovOp_of_mem_harm`: for a conjugation-invariant probability measure `ν` on `SU(2)`, every
  element of `harm k` is an eigenfunction of the walk, with eigenvalue
  `su2Eig ν k = ∫ q₀₀^k dν` (Schur's lemma for the representation of dimension `k + 1`, proved by
  hand);
* `su2Eig_recurrence`, `su2Eig_mul_sin`: if the trace is `ν`-almost surely `2 cos α`, then
  `(k+1) · su2Eig ν k · sin α = sin ((k+1) α)` (the Weyl character formula for `SU(2)`, obtained
  from a three-term recurrence);
* `integral_mul_conj_eq_zero_of_mem_harm`: `harm k ⊥ harm j` in `L²(SU(2))` for `k ≠ j`;
* `su2_class_l2Bound`: for the class measure of `q₀` with `Re (q₀)₀₀ ≥ √2/2`, the walk contracts
  even mean-zero `L²` functions by the factor `(4 (Re (q₀)₀₀)² - 1)/3`.
-/

open MeasureTheory Matrix Real
open scoped ComplexConjugate

namespace SOnMCMC

/-! ### Elements and coercions -/

theorem SU2.coe_mul (x y : SU2) :
    ((x * y : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      = (x : Matrix (Fin 2) (Fin 2) ℂ) * (y : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem SU2.coe_inv (x : SU2) :
    ((x⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = star (x : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem SU2.coe_one : ((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl

/-- The diagonal element `diag(e^{iφ}, e^{-iφ})`. -/
noncomputable def torus (φ : ℝ) : SU2 :=
  SU2.mk' (Complex.exp (φ * Complex.I)) 0 (by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp)

theorem torus_coe (φ : ℝ) : ((torus φ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
    = !![Complex.exp (φ * Complex.I), 0; 0, Complex.exp (-(φ * Complex.I))] := by
  rw [torus, SU2.mk'_coe, ← Complex.exp_conj]
  simp

theorem torus_conj_00 (φ : ℝ) (q : SU2) :
    ((torus φ * q * (torus φ)⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0
      = (q : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
  rw [SU2.coe_mul, SU2.coe_mul, SU2.coe_inv, torus_coe]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, star_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_zero, mul_zero,
    add_zero, zero_mul, RCLike.star_def, ← Complex.exp_conj]
  have h : Complex.exp (φ * Complex.I) * Complex.exp (conj ((φ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    simp
  linear_combination ((q : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * h

theorem torus_conj_10 (φ : ℝ) (q : SU2) :
    ((torus φ * q * (torus φ)⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 1 0
      = Complex.exp (-(2 * φ * Complex.I)) * (q : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
  rw [SU2.coe_mul, SU2.coe_mul, SU2.coe_inv, torus_coe]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, star_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_zero, mul_zero,
    add_zero, zero_mul, zero_add, RCLike.star_def, ← Complex.exp_conj]
  have h : Complex.exp (-(2 * φ * Complex.I))
      = Complex.exp (-(φ * Complex.I)) * Complex.exp (conj ((φ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    simp
    ring
  rw [h]
  ring

theorem integrable_of_continuous_su2 (ν : Measure SU2) [IsFiniteMeasure ν] {F : SU2 → ℂ}
    (hF : Continuous F) : Integrable F ν :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem continuous_coord (i j : Fin 2) :
    Continuous fun q : SU2 => (q : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  continuous_subtype_val.matrix_elem i j

/-! ### Schur's lemma by hand -/

/-- The eigenvalue of the walk on `harm k`: `λ_k(ν) = ∫ q₀₀^k dν`. -/
noncomputable def su2Eig (ν : Measure SU2) (k : ℕ) : ℂ :=
  ∫ q : SU2, (q : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ k ∂ν

theorem su2Eig_zero (ν : Measure SU2) [IsProbabilityMeasure ν] : su2Eig ν 0 = 1 := by
  simp [su2Eig]

/-- Invariance of integrals under conjugation. -/
theorem integral_conj_eq (ν : Measure SU2) (hν : IsConjInvariant ν) (g : SU2) {F : SU2 → ℂ}
    (hF : Continuous F) : ∫ q, F (g * q * g⁻¹) ∂ν = ∫ q, F q ∂ν := by
  have h := integral_map (μ := ν) (measurable_conj_right g).aemeasurable
    (f := F) hF.aestronglyMeasurable
  rw [hν g] at h
  exact h.symm

/-- Mixed moments of the first column vanish, by invariance under the diagonal torus. -/
theorem integral_mixed_eq_zero (ν : Measure SU2) (hν : IsConjInvariant ν) (a : ℕ) {j : ℕ}
    (hj : 0 < j) :
    ∫ q : SU2, (q : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ a * (q : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ^ j ∂ν
      = 0 := by
  set F : SU2 → ℂ := fun q =>
    (q : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ a * (q : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ^ j with hF
  have hFc : Continuous F := ((continuous_coord 0 0).pow a).mul ((continuous_coord 1 0).pow j)
  have h := integral_conj_eq ν hν (torus (π / (2 * j))) hFc
  have hj' : (j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
  have hneg : ∀ q : SU2, F (torus (π / (2 * j)) * q * (torus (π / (2 * j)))⁻¹) = -F q := by
    intro q
    simp only [hF, torus_conj_00, torus_conj_10, mul_pow, ← Complex.exp_nat_mul]
    have : Complex.exp ((j : ℂ) * -(2 * ((π / (2 * j) : ℝ) : ℂ) * Complex.I)) = -1 := by
      have e : (j : ℂ) * -(2 * ((π / (2 * j) : ℝ) : ℂ) * Complex.I) = -(π * Complex.I) := by
        push_cast
        field_simp
      rw [e, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [this]
    ring
  simp only [hneg] at h
  rw [integral_neg] at h
  have h2 : (2 : ℂ) * ∫ q, F q ∂ν = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The torus step: `∫ (w₀ q₀₀ + w₁ q₁₀)^k dν = w₀^k λ_k`. -/
theorem integral_first_column_pow (ν : Measure SU2) [IsFiniteMeasure ν] (hν : IsConjInvariant ν)
    (w0 w1 : ℂ) (k : ℕ) :
    ∫ q : SU2, (w1 * (q : Matrix (Fin 2) (Fin 2) ℂ) 1 0
        + w0 * (q : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ k ∂ν = w0 ^ k * su2Eig ν k := by
  simp only [add_pow]
  rw [integral_finsetSum]
  · rw [Finset.sum_eq_single 0]
    · simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
        mul_pow]
      rw [integral_const_mul, su2Eig]
    · intro m _ hm
      have hm' : 0 < m := Nat.pos_of_ne_zero hm
      have : ∀ q : SU2, (w1 * (q : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ^ m
            * (w0 * (q : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ (k - m) * (k.choose m : ℂ)
          = (w1 ^ m * w0 ^ (k - m) * (k.choose m : ℂ))
            * ((q : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ (k - m)
              * (q : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ^ m) := by
        intro q
        ring
      simp only [this]
      rw [integral_const_mul, integral_mixed_eq_zero ν hν (k - m) hm', mul_zero]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
  · intro m _
    refine integrable_of_continuous_su2 ν ?_
    exact (((continuous_const.mul (continuous_coord 1 0)).pow m).mul
      ((continuous_const.mul (continuous_coord 0 0)).pow (k - m))).mul continuous_const

/-- Every nonzero vector of `ℂ²` is a multiple of the first column of an element of `SU(2)`. -/
theorem exists_su2_first_column {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    ∃ (g : SU2) (r : ℂ), r ≠ 0 ∧ v 0 = r * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ∧
      v 1 = r * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
  set N : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1) with hN
  have hNpos : 0 < N := by
    have h0 := Complex.normSq_nonneg (v 0)
    have h1 := Complex.normSq_nonneg (v 1)
    rcases (add_nonneg h0 h1).eq_or_lt with h | h
    · exfalso
      apply hv
      have e0 : Complex.normSq (v 0) = 0 := by linarith
      have e1 : Complex.normSq (v 1) = 0 := by linarith
      funext i
      fin_cases i
      · exact Complex.normSq_eq_zero.mp e0
      · exact Complex.normSq_eq_zero.mp e1
    · exact h
  set r : ℝ := √N with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hNpos
  have hr2 : r ^ 2 = N := Real.sq_sqrt hNpos.le
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hcond : v 0 / r * conj (v 0 / r) + -conj (v 1) / r * conj (-conj (v 1) / r) = 1 := by
    have h1 : v 0 * conj (v 0) = (Complex.normSq (v 0) : ℂ) := Complex.mul_conj (v 0)
    have h2 : v 1 * conj (v 1) = (Complex.normSq (v 1) : ℂ) := Complex.mul_conj (v 1)
    have h3 : (r : ℂ) ^ 2 = (Complex.normSq (v 0) : ℂ) + (Complex.normSq (v 1) : ℂ) := by
      rw [← Complex.ofReal_pow, hr2, hN]
      push_cast
      ring
    simp only [map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal]
    field_simp
    linear_combination h1 + h2 - h3
  refine ⟨SU2.mk' (v 0 / r) (-conj (v 1) / r) hcond, r, hrc, ?_, ?_⟩
  · simp only [SU2.mk'_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one]
    field_simp
  · simp only [SU2.mk'_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, map_div₀, map_neg, Complex.conj_conj,
      Complex.conj_ofReal]
    field_simp

/-- **Schur's lemma for `Sym^k ℂ²`, by hand:** `∫ (wᵀ q v)^k dν = λ_k (wᵀ v)^k`. -/
theorem integral_lin_pow (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    (w v : Fin 2 → ℂ) (k : ℕ) :
    ∫ q : SU2, lin w v q ^ k ∂ν = su2Eig ν k * (w ⬝ᵥ v) ^ k := by
  by_cases hv : v = 0
  · subst hv
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [su2Eig]
    · simp [lin, zero_pow hk.ne']
  · obtain ⟨g, r, hr, h0, h1⟩ := exists_su2_first_column hv
    have hFc : Continuous fun q : SU2 => lin w v q ^ k := (continuous_lin w v).pow k
    rw [← integral_conj_eq ν hν g hFc]
    -- `g⁻¹ v = r e₀`
    have hginv : star (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = ![r, 0] := by
      have hsg : star (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
        mem_unitaryGroup_iff'.mp (SU2.coe_mem_unitary g)
      have hv' : v = (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![r, 0] := by
        funext i
        fin_cases i
        · simp [mulVec, dotProduct, Fin.sum_univ_two, h0, mul_comm]
        · simp [mulVec, dotProduct, Fin.sum_univ_two, h1, mul_comm]
      rw [hv', mulVec_mulVec, hsg, one_mulVec]
    have hpt : ∀ q : SU2, lin w v (g * q * g⁻¹)
        = r * ((w ᵥ* (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 * (q : Matrix (Fin 2) (Fin 2) ℂ) 1 0
          + (w ᵥ* (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 * (q : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
      intro q
      have : lin w v (g * q * g⁻¹) = (w ᵥ* (g : Matrix (Fin 2) (Fin 2) ℂ))
          ⬝ᵥ ((q : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![r, 0]) := by
        show w ⬝ᵥ (((g : Matrix (Fin 2) (Fin 2) ℂ) * (q : Matrix (Fin 2) (Fin 2) ℂ)
          * star (g : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ v) = _
        rw [← mulVec_mulVec, hginv, ← mulVec_mulVec, dotProduct_mulVec]
      rw [this]
      simp [dotProduct, mulVec, Fin.sum_univ_two]
      ring
    simp only [hpt, mul_pow]
    rw [integral_const_mul, integral_first_column_pow ν hν]
    have hw0 : (w ᵥ* (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 * r = w ⬝ᵥ v := by
      simp only [vecMul, dotProduct, Fin.sum_univ_two, h0, h1]
      ring
    rw [← hw0]
    ring

/-- **Powers of linear forms are eigenfunctions.** -/
theorem markovOp_lin_pow (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    (u v : Fin 2 → ℂ) (k : ℕ) : markovOp ν (lin u v ^ k) = su2Eig ν k • lin u v ^ k := by
  funext x
  simp only [markovOp, Pi.pow_apply, Pi.smul_apply, smul_eq_mul, lin_mul]
  rw [integral_lin_pow ν hν]
  congr 2
  rw [lin, dotProduct_mulVec]

/-- **Every element of `harm k` is an eigenfunction** of a conjugation-invariant walk, with
eigenvalue `su2Eig ν k`. -/
theorem markovOp_of_mem_harm (ν : Measure SU2) [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    {k : ℕ} {F : SU2 → ℂ} (hF : F ∈ harm k) : markovOp ν F = su2Eig ν k • F := by
  have hint : ∀ {H : SU2 → ℂ}, Continuous H → ∀ x : SU2, Integrable (fun q => H (x * q)) ν :=
    fun hH x => integrable_of_continuous_su2 ν (hH.comp (continuous_const.mul continuous_id))
  have key : Continuous F ∧ markovOp ν F = su2Eig ν k • F := by
    refine Submodule.span_induction
      (p := fun F _ => Continuous F ∧ markovOp ν F = su2Eig ν k • F) ?_ ?_ ?_ ?_ hF
    · rintro _ ⟨⟨u, v⟩, rfl⟩
      exact ⟨(continuous_lin u v).pow k, markovOp_lin_pow ν hν u v k⟩
    · refine ⟨continuous_const, ?_⟩
      funext x
      simp [markovOp]
    · rintro a b _ _ ⟨hac, ha⟩ ⟨hbc, hb⟩
      refine ⟨hac.add hbc, ?_⟩
      funext x
      have h1 : markovOp ν (a + b) x = markovOp ν a x + markovOp ν b x := by
        simp only [markovOp, Pi.add_apply]
        exact integral_add (hint hac x) (hint hbc x)
      rw [h1, ha, hb]
      simp [mul_add]
    · rintro c a _ ⟨hac, ha⟩
      refine ⟨hac.const_smul c, ?_⟩
      funext x
      have h1 : markovOp ν (c • a) x = c * markovOp ν a x := by
        simp only [markovOp, Pi.smul_apply, smul_eq_mul]
        exact integral_const_mul c _
      rw [h1, ha]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  exact key.2

end SOnMCMC

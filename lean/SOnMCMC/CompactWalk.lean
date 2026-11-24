import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Moments.Variance

/-!
# Random walks on measurable groups with an invariant probability measure

Paper: Section 2.2 ("Random walks on compact groups").

`G` is a measurable group, `m` a right-invariant probability measure on `G` (Haar measure when
`G` is compact) and `ν` a probability measure on `G` (the step distribution).  The Markov operator
is `(P f)(x) = ∫ f (x * g) dν(g)`.  We prove, for honest `L²(m)` functions:

* `m` is stationary: `∫ P f dm = ∫ f dm`;
* `P` is an `L²(m)` contraction;
* `P` is symmetric when `ν` is invariant under inversion (reversibility);
* matrix coefficients of a representation `π` are mapped to matrix coefficients of `π · ν̂(π)`,
  where `ν̂(π) = ∫ π dν`; eigenvectors of `ν̂(π)` give eigenfunctions of `P`;
* `ν̂(π)` is fixed by every symmetry of `ν` that acts on `π` by conjugation.

We also define the Poincaré inequality / spectral gap and the `L²` contraction coefficient, and
show that Haar measure on a compact group is right-invariant.

Everything about `markovOp` in the first sections is stated with `@[to_additive]`, so that it is
also available for additive groups such as the circle `ℝ / 2πℤ`.
-/

open MeasureTheory Measure
open scoped ENNReal ComplexConjugate

namespace SOnMCMC

section Jensen

variable {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Jensen's inequality for the square of the norm of an integral against a probability measure. -/
theorem norm_integral_sq_le (ν : Measure α) [IsProbabilityMeasure ν] {φ : α → E}
    (hφ : MemLp φ 2 ν) : ‖∫ a, φ a ∂ν‖ ^ 2 ≤ ∫ a, ‖φ a‖ ^ 2 ∂ν := by
  have hu : MemLp (fun a => ‖φ a‖) 2 ν := hφ.norm
  have h1 : ‖∫ a, φ a ∂ν‖ ≤ ∫ a, ‖φ a‖ ∂ν := norm_integral_le_integral_norm _
  have h2 : (∫ a, ‖φ a‖ ∂ν) ^ 2 ≤ ∫ a, ‖φ a‖ ^ 2 ∂ν := by
    have hv := ProbabilityTheory.variance_nonneg (fun a => ‖φ a‖) ν
    rw [ProbabilityTheory.variance_eq_sub hu] at hv
    have : ∫ a, ((fun a => ‖φ a‖) ^ 2) a ∂ν = ∫ a, ‖φ a‖ ^ 2 ∂ν := rfl
    linarith
  calc ‖∫ a, φ a ∂ν‖ ^ 2 ≤ (∫ a, ‖φ a‖ ∂ν) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

omit [NormedSpace ℝ E] in
/-- If `‖F‖²` is dominated almost everywhere by an integrable function, then `F ∈ L²` and
`∫ ‖F‖² ≤ ∫ Q`. -/
theorem memLp_two_of_sq_le {μ : Measure α} {F : α → E} (hmeas : AEStronglyMeasurable F μ)
    {Q : α → ℝ} (hQ : Integrable Q μ) (hb : ∀ᵐ x ∂μ, ‖F x‖ ^ 2 ≤ Q x) :
    MemLp F 2 μ ∧ ∫ x, ‖F x‖ ^ 2 ∂μ ≤ ∫ x, Q x ∂μ := by
  have hPsq : Integrable (fun x => ‖F x‖ ^ 2) μ := by
    refine Integrable.mono' hQ (hmeas.norm.pow 2) ?_
    filter_upwards [hb] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hx
  exact ⟨(memLp_two_iff_integrable_sq_norm hmeas).mpr hPsq, integral_mono_ae hPsq hQ hb⟩

/-- Cauchy–Schwarz in the form used below: if `∫ g² ≤ ρ² ∫ f²` then `∫ f g ≤ ρ ∫ f²`. -/
theorem integral_mul_le_of_sq_le {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hb : ∫ x, g x ^ 2 ∂μ ≤ ρ ^ 2 * ∫ x, f x ^ 2 ∂μ) :
    ∫ x, f x * g x ∂μ ≤ ρ * ∫ x, f x ^ 2 ∂μ := by
  have hf2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hg2 : Integrable (fun x => g x ^ 2) μ := hg.integrable_sq
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hB0 : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rcases hρ0.eq_or_lt with h0 | hpos
  · -- ρ = 0: g = 0 a.e.
    subst h0
    have hB : ∫ x, g x ^ 2 ∂μ = 0 := by
      have : ∫ x, g x ^ 2 ∂μ ≤ 0 := by simpa using hb
      exact le_antisymm this hB0
    have hae : (fun x => g x ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hg2).mp hB
    have : ∫ x, f x * g x ∂μ = 0 := by
      rw [← integral_zero α ℝ (μ := μ)]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      have : g x = 0 := by simpa using hx
      simp [this]
    rw [this]
    simp
  · -- ρ > 0: weighted AM-GM, `2 f g ≤ ρ f² + g²/ρ`.
    have hpt : ∀ x, f x * g x ≤ ρ / 2 * f x ^ 2 + 1 / (2 * ρ) * g x ^ 2 := by
      intro x
      have h := sq_nonneg (ρ * f x - g x)
      have : f x * g x
          = (ρ / 2 * f x ^ 2 + 1 / (2 * ρ) * g x ^ 2) - 1 / (2 * ρ) * (ρ * f x - g x) ^ 2 := by
        field_simp
        ring
      rw [this]
      have : 0 ≤ 1 / (2 * ρ) * (ρ * f x - g x) ^ 2 := by positivity
      linarith
    have hint : Integrable (fun x => ρ / 2 * f x ^ 2 + 1 / (2 * ρ) * g x ^ 2) μ :=
      (hf2.const_mul _).add (hg2.const_mul _)
    calc ∫ x, f x * g x ∂μ
        ≤ ∫ x, ρ / 2 * f x ^ 2 + 1 / (2 * ρ) * g x ^ 2 ∂μ := integral_mono hfg hint hpt
      _ = ρ / 2 * ∫ x, f x ^ 2 ∂μ + 1 / (2 * ρ) * ∫ x, g x ^ 2 ∂μ := by
          rw [integral_add (hf2.const_mul _) (hg2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ ρ / 2 * ∫ x, f x ^ 2 ∂μ + 1 / (2 * ρ) * (ρ ^ 2 * ∫ x, f x ^ 2 ∂μ) := by
          have : 0 ≤ 1 / (2 * ρ) := by positivity
          have := mul_le_mul_of_nonneg_left hb this
          linarith
      _ = ρ * ∫ x, f x ^ 2 ∂μ := by
          field_simp
          ring

end Jensen

section Markov

variable {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Markov operator of the right random walk on `G` with step distribution `ν`:
`(P f)(x) = ∫ f (x * g) dν(g)`. -/
@[to_additive addMarkovOp /-- The Markov operator of the random walk on an additive group `G`
with step distribution `ν`: `(P f)(x) = ∫ f (x + g) dν(g)`. -/]
noncomputable def markovOp (ν : Measure G) (f : G → E) : G → E := fun x => ∫ g, f (x * g) ∂ν

omit [MeasurableMul₂ G] in
@[to_additive addMarkovOp_apply]
theorem markovOp_apply (ν : Measure G) (f : G → E) (x : G) :
    markovOp ν f x = ∫ g, f (x * g) ∂ν := rfl

omit [MeasurableMul₂ G] in
/-- Constants are fixed by the Markov operator. -/
@[to_additive addMarkovOp_const]
theorem markovOp_const [CompleteSpace E] (ν : Measure G) [IsProbabilityMeasure ν] (c : E) :
    markovOp ν (fun _ => c) = fun _ => c := by
  funext x
  simp only [markovOp, integral_const, probReal_univ, one_smul]

variable (m ν : Measure G) [SFinite m] [IsFiniteMeasure ν] [m.IsMulRightInvariant]

omit [NormedSpace ℝ E] in
@[to_additive]
theorem integrable_comp_mul {f : G → E} (hf : Integrable f m) :
    Integrable (fun z : G × G => f (z.1 * z.2)) (m.prod ν) :=
  (measurePreserving_mul_prod m ν).integrable_comp_of_integrable (hf.comp_fst ν)

omit [NormedSpace ℝ E] in
@[to_additive]
theorem memLp_comp_mul {f : G → E} {p : ℝ≥0∞} (hf : MemLp f p m) :
    MemLp (fun z : G × G => f (z.1 * z.2)) p (m.prod ν) :=
  (hf.comp_fst ν).comp_measurePreserving (measurePreserving_mul_prod m ν)

/-- The Markov operator maps integrable functions to integrable functions. -/
@[to_additive integrable_addMarkovOp]
theorem integrable_markovOp {f : G → E} (hf : Integrable f m) :
    Integrable (markovOp ν f) m :=
  (integrable_comp_mul m ν hf).integral_prod_left

/-- **Stationarity.** A right-invariant measure is stationary for the walk. -/
@[to_additive integral_addMarkovOp]
theorem integral_markovOp [CompleteSpace E] [IsProbabilityMeasure ν] {f : G → E}
    (hf : Integrable f m) :
    ∫ x, markovOp ν f x ∂m = ∫ x, f x ∂m := by
  have hint := integrable_comp_mul m ν hf
  have hT := measurePreserving_mul_prod m ν
  calc ∫ x, markovOp ν f x ∂m = ∫ z, f (z.1 * z.2) ∂(m.prod ν) := (integral_prod _ hint).symm
    _ = ∫ z, f z.1 ∂(m.prod ν) := by
        have h1 : AEStronglyMeasurable (fun z : G × G => f z.1)
            (Measure.map (fun z : G × G => (z.1 * z.2, z.2)) (m.prod ν)) := by
          rw [hT.map_eq]
          exact (hf.comp_fst ν).aestronglyMeasurable
        have := integral_map hT.aemeasurable h1
        rw [hT.map_eq] at this
        exact this.symm
    _ = ∫ x, f x ∂m := by
        rw [integral_prod _ (hf.comp_fst ν)]
        simp only [integral_const, probReal_univ, one_smul]

/-- **`L²` contraction.** The Markov operator maps `L²(m)` to itself and does not increase the
`L²` norm. -/
@[to_additive memLp_addMarkovOp_and_le]
theorem memLp_markovOp_and_le [IsProbabilityMeasure m] [IsProbabilityMeasure ν]
    {f : G → E} (hf : MemLp f 2 m) :
    MemLp (markovOp ν f) 2 m ∧ ∫ x, ‖markovOp ν f x‖ ^ 2 ∂m ≤ ∫ x, ‖f x‖ ^ 2 ∂m := by
  have hf1 : Integrable f m := hf.integrable one_le_two
  have hmeas : AEStronglyMeasurable (markovOp ν f) m :=
    (integrable_markovOp m ν hf1).aestronglyMeasurable
  have hsq : Integrable (fun x => ‖f x‖ ^ 2) m :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hsq2 : Integrable (fun z : G × G => ‖f (z.1 * z.2)‖ ^ 2) (m.prod ν) :=
    integrable_comp_mul m ν hsq
  have hint := integrable_comp_mul m ν hf1
  have hQ : Integrable (fun x => ∫ g, ‖f (x * g)‖ ^ 2 ∂ν) m := hsq2.integral_prod_left
  have hbound : ∀ᵐ x ∂m, ‖markovOp ν f x‖ ^ 2 ≤ ∫ g, ‖f (x * g)‖ ^ 2 ∂ν := by
    filter_upwards [hsq2.prod_right_ae, hint.prod_right_ae] with x hx hx'
    have hmem : MemLp (fun g => f (x * g)) 2 ν :=
      (memLp_two_iff_integrable_sq_norm hx'.aestronglyMeasurable).mpr hx
    exact norm_integral_sq_le ν hmem
  have key := memLp_two_of_sq_le hmeas hQ hbound
  exact ⟨key.1, key.2.trans_eq (integral_markovOp m ν hsq)⟩

@[to_additive memLp_addMarkovOp]
theorem memLp_markovOp [IsProbabilityMeasure m] [IsProbabilityMeasure ν]
    {f : G → E} (hf : MemLp f 2 m) : MemLp (markovOp ν f) 2 m :=
  (memLp_markovOp_and_le m ν hf).1

/-- The Markov operator is an `L²(m)` contraction. -/
@[to_additive integral_norm_sq_addMarkovOp_le]
theorem integral_norm_sq_markovOp_le [IsProbabilityMeasure m] [IsProbabilityMeasure ν]
    {f : G → E} (hf : MemLp f 2 m) :
    ∫ x, ‖markovOp ν f x‖ ^ 2 ∂m ≤ ∫ x, ‖f x‖ ^ 2 ∂m :=
  (memLp_markovOp_and_le m ν hf).2

/-- **Reversibility.** If the step distribution is invariant under inversion, the Markov operator
is symmetric on `L²(m)`. -/
@[to_additive (dont_translate := 𝕜) integral_addMarkovOp_mul]
theorem integral_markovOp_mul {𝕜 : Type*} [RCLike 𝕜] [MeasurableInv G] [ν.IsInvInvariant]
    {f h : G → 𝕜} (hf : MemLp f 2 m) (hh : MemLp h 2 m) :
    ∫ x, markovOp ν f x * h x ∂m = ∫ x, f x * markovOp ν h x ∂m := by
  have hT := measurePreserving_div_prod m ν
  have hF : Integrable (fun z : G × G => f (z.1 * z.2) * h z.1) (m.prod ν) :=
    (memLp_comp_mul m ν hf).integrable_mul (hh.comp_fst ν)
  have hF' : Integrable (fun z : G × G => f z.1 * h (z.1 / z.2)) (m.prod ν) := by
    have := hT.integrable_comp_of_integrable hF
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Function.comp]
  calc ∫ x, markovOp ν f x * h x ∂m
      = ∫ x, ∫ g, f (x * g) * h x ∂ν ∂m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [markovOp]
        rw [integral_mul_const]
    _ = ∫ z, f (z.1 * z.2) * h z.1 ∂(m.prod ν) := (integral_prod _ hF).symm
    _ = ∫ z, f z.1 * h (z.1 / z.2) ∂(m.prod ν) := by
        have h1 : AEStronglyMeasurable (fun z : G × G => f (z.1 * z.2) * h z.1)
            (Measure.map (fun z : G × G => (z.1 / z.2, z.2)) (m.prod ν)) := by
          rw [hT.map_eq]
          exact hF.aestronglyMeasurable
        have := integral_map hT.aemeasurable h1
        rw [hT.map_eq] at this
        rw [this]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp
    _ = ∫ x, ∫ g, f x * h (x / g) ∂ν ∂m := integral_prod _ hF'
    _ = ∫ x, f x * markovOp ν h x ∂m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [markovOp]
        rw [integral_const_mul]
        congr 1
        have := integral_inv_eq_self (fun g => h (x * g)) ν
        simpa [div_eq_mul_inv] using this

end Markov

section Fourier

variable {G : Type*} [MeasurableSpace G] [Group G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]

/-- The Fourier transform of a measure `ν` at a matrix-valued function `π` (in practice a
representation): the entrywise integral `ν̂(π) = ∫ π dν`. -/
noncomputable def fourierMat (ν : Measure G) (π : G → Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  Matrix.of fun i j => ∫ g, π g i j ∂ν

omit [Group G] [Fintype ι] [DecidableEq ι] in
@[simp]
theorem fourierMat_apply (ν : Measure G) (π : G → Matrix ι ι 𝕜) (i j : ι) :
    fourierMat ν π i j = ∫ g, π g i j ∂ν := rfl

/-- **Matrix coefficients are invariant.** `P π_{ij} = (π · ν̂(π))_{ij}`. -/
theorem markovOp_matrixCoeff (ν : Measure G) (π : G →* Matrix ι ι 𝕜)
    (hπ : ∀ i j, Integrable (fun g => π g i j) ν) (i j : ι) :
    markovOp ν (fun x => π x i j) = fun x => (π x * fourierMat ν π) i j := by
  funext x
  simp only [markovOp, map_mul, Matrix.mul_apply, fourierMat_apply]
  rw [integral_finsetSum _ (fun k _ => (hπ k j).const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]

/-- **Eigenvectors of the Fourier transform give eigenfunctions of the walk.** -/
theorem markovOp_eigenfunction (ν : Measure G) (π : G →* Matrix ι ι 𝕜)
    (hπ : ∀ i j, Integrable (fun g => π g i j) ν) (v : ι → 𝕜) (c : 𝕜)
    (hv : (fourierMat ν π).mulVec v = c • v) (i : ι) :
    markovOp ν (fun x => (π x).mulVec v i) = fun x => c * (π x).mulVec v i := by
  funext x
  have h1 : markovOp ν (fun y => (π y).mulVec v i) x
      = ∑ j, markovOp ν (fun y => π y i j) x * v j := by
    simp only [markovOp, Matrix.mulVec, dotProduct]
    rw [integral_finsetSum _ (fun j _ => ?_)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const]
    · have : Integrable (fun g => π (x * g) i j) ν := by
        simp only [map_mul, Matrix.mul_apply]
        exact integrable_finsetSum _ (fun k _ => (hπ k j).const_mul _)
      exact this.mul_const _
  rw [h1]
  simp only [markovOp_matrixCoeff ν π hπ]
  have h2 : ∑ j, (π x * fourierMat ν π) i j * v j = ((π x * fourierMat ν π).mulVec v) i := rfl
  rw [h2, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rfl

omit [Group G] [DecidableEq ι] in
/-- **Symmetries of the step distribution constrain its Fourier transform.**
If `φ` preserves `ν` and `π ∘ φ = B π B'`, then `ν̂(π) = B ν̂(π) B'`. -/
theorem fourierMat_eq_conj (ν : Measure G) (π : G → Matrix ι ι 𝕜)
    (hπ : ∀ i j, Integrable (fun g => π g i j) ν) (φ : G → G) (hφ : MeasurePreserving φ ν ν)
    (B B' : Matrix ι ι 𝕜) (h : ∀ g, π (φ g) = B * π g * B') :
    fourierMat ν π = B * fourierMat ν π * B' := by
  ext i j
  have h1 : ∫ g, π g i j ∂ν = ∫ g, π (φ g) i j ∂ν := by
    have hm : AEStronglyMeasurable (fun g => π g i j) (Measure.map φ ν) := by
      rw [hφ.map_eq]
      exact (hπ i j).aestronglyMeasurable
    have := integral_map hφ.aemeasurable hm
    rw [hφ.map_eq] at this
    exact this
  rw [fourierMat_apply, h1]
  simp only [h, Matrix.mul_apply, fourierMat_apply, Finset.sum_mul]
  rw [integral_finsetSum _ (fun l _ => ?_)]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ (fun k _ => ?_)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_mul_const, integral_const_mul]
    · exact ((hπ k l).const_mul _).mul_const _
  · exact integrable_finsetSum _ (fun k _ => ((hπ k l).const_mul _).mul_const _)

end Fourier

section Gap

variable {G : Type*} [MeasurableSpace G] [Group G]

/-- **Poincaré inequality.** The `ν`-walk with stationary measure `m` satisfies a Poincaré
inequality with constant `γ` if `⟨f, P f⟩ ≤ (1 - γ) ⟨f, f⟩` for every real `f ∈ L²(m)` of mean
zero.  Equivalently `γ · Var(f) ≤ ⟨f, (I - P) f⟩`, the Dirichlet form. -/
@[to_additive AddPoincareIneq /-- Poincaré inequality for a walk on an additive group. -/]
def PoincareIneq (m ν : Measure G) (γ : ℝ) : Prop :=
  ∀ f : G → ℝ, MemLp f 2 m → ∫ x, f x ∂m = 0 →
    ∫ x, f x * markovOp ν f x ∂m ≤ (1 - γ) * ∫ x, f x ^ 2 ∂m

/-- **Spectral gap.** `γ` is the spectral gap of the walk if it is the largest constant in the
Poincaré inequality. -/
@[to_additive IsAddSpectralGap /-- Spectral gap of a walk on an additive group. -/]
def IsSpectralGap (m ν : Measure G) (γ : ℝ) : Prop := IsGreatest {γ' | PoincareIneq m ν γ'} γ

/-- **`L²` contraction coefficient.** `ρ` bounds the operator norm of `P` on mean-zero complex
`L²(m)` functions: `‖P f‖₂ ≤ ρ ‖f‖₂`. -/
@[to_additive AddL2ContractionBound
/-- `L²` contraction bound for a walk on an additive group. -/]
def L2ContractionBound (m ν : Measure G) (ρ : ℝ) : Prop :=
  ∀ f : G → ℂ, MemLp f 2 m → ∫ x, f x ∂m = 0 →
    ∫ x, ‖markovOp ν f x‖ ^ 2 ∂m ≤ ρ ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂m

/-- **An eigenfunction bounds the spectral gap from above.** If `f` is a nonzero mean-zero real
`L²` eigenfunction with eigenvalue `lam`, every Poincaré constant is at most `1 - lam`. -/
@[to_additive]
theorem PoincareIneq.le_of_eigenfunction {m ν : Measure G} {γ : ℝ} (hγ : PoincareIneq m ν γ)
    {f : G → ℝ} (hf : MemLp f 2 m) (hmean : ∫ x, f x ∂m = 0) (hpos : 0 < ∫ x, f x ^ 2 ∂m)
    {lam : ℝ} (heig : markovOp ν f = fun x => lam * f x) : γ ≤ 1 - lam := by
  have h := hγ f hf hmean
  have h2 : ∫ x, f x * markovOp ν f x ∂m = lam * ∫ x, f x ^ 2 ∂m := by
    rw [heig, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [h2] at h
  by_contra hlt
  push Not at hlt
  nlinarith

variable [MeasurableMul₂ G]

/-- An `L²` contraction bound gives a Poincaré inequality: `gap ≥ 1 - ρ`. -/
@[to_additive AddL2ContractionBound.addPoincareIneq]
theorem L2ContractionBound.poincareIneq {m ν : Measure G} [IsProbabilityMeasure m]
    [IsProbabilityMeasure ν] [m.IsMulRightInvariant] {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : L2ContractionBound m ν ρ) : PoincareIneq m ν (1 - ρ) := by
  intro f hf hmean
  -- pass to the complexification
  have hfc : MemLp (fun x => (f x : ℂ)) 2 m := hf.ofReal
  have hmeanc : ∫ x, (f x : ℂ) ∂m = 0 := by
    rw [integral_complex_ofReal, hmean, Complex.ofReal_zero]
  have hPc : markovOp ν (fun x => (f x : ℂ)) = fun x => ((markovOp ν f x : ℝ) : ℂ) := by
    funext x
    simp only [markovOp]
    exact integral_complex_ofReal
  have hb := hρ _ hfc hmeanc
  simp only [hPc, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hb
  have hPf : MemLp (markovOp ν f) 2 m := memLp_markovOp m ν hf
  rw [sub_sub_cancel]
  exact integral_mul_le_of_sq_le hf hPf hρ0 hb

end Gap

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Haar measure on a compact group is right-invariant** (compact groups are unimodular). -/
theorem isMulRightInvariant_of_compact (m : Measure G) [IsHaarMeasure m] :
    m.IsMulRightInvariant := by
  constructor
  intro g
  have hfin : IsFiniteMeasure m := ⟨isCompact_univ.measure_lt_top⟩
  have h := isMulInvariant_eq_smul_of_compactSpace (Measure.map (· * g) m) m
  have huniv : (Measure.map (· * g) m) Set.univ = m Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have hpos : m Set.univ ≠ 0 := (IsOpen.measure_pos m isOpen_univ Set.univ_nonempty).ne'
  have hc : (haarScalarFactor (Measure.map (· * g) m) m : ℝ≥0∞) = 1 := by
    have h2 : (Measure.map (· * g) m) Set.univ
        = (haarScalarFactor (Measure.map (· * g) m) m : ℝ≥0∞) * m Set.univ := by
      conv_lhs => rw [h]
      simp
    rw [huniv] at h2
    have h3 : (1 : ℝ≥0∞) * m Set.univ
        = (haarScalarFactor (Measure.map (· * g) m) m : ℝ≥0∞) * m Set.univ := by
      rw [one_mul]
      exact h2
    exact ((ENNReal.mul_left_inj hpos (measure_ne_top m _)).mp h3).symm
  rw [h]
  rw [ENNReal.coe_eq_one] at hc
  rw [hc, one_smul]

end Haar

end SOnMCMC

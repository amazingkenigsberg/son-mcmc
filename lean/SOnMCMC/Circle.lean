import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import SOnMCMC.CompactWalk

/-!
# Random walks on the circle: complete spectral decomposition

Paper: Section 4.1.

On the circle `𝕋 = ℝ / Tℤ` (which is `SO(2)` when `T = 2π`) every step distribution `ν` is
conjugation invariant, the irreducible representations are the characters `e_k = fourier k`, and
the Markov operator is a Fourier multiplier:

* `P e_k = ν̂(k) e_k` with `ν̂(k) = ∫ e_k dν` (`addMarkovOp_fourier`);
* `(P f)^(k) = ν̂(k) f̂(k)` for integrable `f` (`fourierCoeff_addMarkovOp`);
* if `|ν̂(k)| ≤ ρ` for all `k ≠ 0` then `‖P f‖₂ ≤ ρ ‖f‖₂` for mean-zero `f ∈ L²`
  (`circle_l2ContractionBound`), and conversely (`circleChar_le_of_bound`);
* if moreover `ν̂(k₀) = ρ` for some `k₀ ≠ 0`, the spectral gap is exactly `1 - ρ`
  (`circle_isSpectralGap`).
-/

open MeasureTheory AddCircle
open scoped ComplexConjugate

namespace SOnMCMC

section Circle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Fourier–Stieltjes coefficients of the step distribution: `ν̂(k) = ∫ e_k dν`. -/
noncomputable def circleChar (ν : Measure (AddCircle T)) (k : ℤ) : ℂ := ∫ y, fourier k y ∂ν

omit hT in
theorem fourier_add_arg (n : ℤ) (x y : AddCircle T) :
    (fourier n (x + y) : ℂ) = fourier n x * fourier n y := by
  simp [fourier_apply, toCircle_add]

omit hT in
theorem norm_fourier_apply (n : ℤ) (x : AddCircle T) : ‖(fourier n x : ℂ)‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

omit hT in
theorem fourier_mul_fourier_neg (k : ℤ) (y : AddCircle T) :
    (fourier k y : ℂ) * fourier (-k) y = 1 := by
  rw [← fourier_add, add_neg_cancel, fourier_zero]

omit hT in
theorem norm_circleChar_le (ν : Measure (AddCircle T)) [IsProbabilityMeasure ν] (k : ℤ) :
    ‖circleChar ν k‖ ≤ 1 := by
  calc ‖∫ y, (fourier k y : ℂ) ∂ν‖ ≤ ∫ y, ‖(fourier k y : ℂ)‖ ∂ν :=
        norm_integral_le_integral_norm _
    _ = 1 := by
        simp only [norm_fourier_apply, integral_const, probReal_univ, smul_eq_mul, mul_one]

omit hT in
/-- **Characters are eigenfunctions:** `P e_k = ν̂(k) e_k`. -/
theorem addMarkovOp_fourier (ν : Measure (AddCircle T)) (k : ℤ) :
    addMarkovOp ν (fun x => (fourier k x : ℂ)) = fun x => circleChar ν k * fourier k x := by
  funext x
  simp only [addMarkovOp, circleChar, fourier_add_arg]
  rw [integral_const_mul, mul_comm]

/-- **The walk is a Fourier multiplier:** `(P f)^(k) = ν̂(k) f̂(k)`. -/
theorem fourierCoeff_addMarkovOp (ν : Measure (AddCircle T)) [IsProbabilityMeasure ν]
    {f : AddCircle T → ℂ} (hf : Integrable f haarAddCircle) (k : ℤ) :
    fourierCoeff (addMarkovOp ν f) k = circleChar ν k * fourierCoeff f k := by
  have hprod : Integrable
      (fun z : AddCircle T × AddCircle T => (fourier (-k) z.1 : ℂ) * f (z.1 + z.2))
      ((haarAddCircle : Measure (AddCircle T)).prod ν) := by
    refine (integrable_comp_add haarAddCircle ν hf).bdd_mul (c := 1) ?_ ?_
    · exact ((fourier (-k)).continuous.comp continuous_fst).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => (norm_fourier_apply _ _).le
  calc fourierCoeff (addMarkovOp ν f) k
      = ∫ x, ∫ y, (fourier (-k) x : ℂ) * f (x + y) ∂ν ∂haarAddCircle := by
        simp only [fourierCoeff, addMarkovOp, smul_eq_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [integral_const_mul]
    _ = ∫ y, ∫ x, (fourier (-k) x : ℂ) * f (x + y) ∂haarAddCircle ∂ν :=
        integral_integral_swap hprod
    _ = ∫ y, (fourier k y : ℂ) * fourierCoeff f k ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        have h1 : ∀ x : AddCircle T, (fourier (-k) x : ℂ) * f (x + y)
            = fourier k y * (fourier (-k) (x + y) * f (x + y)) := by
          intro x
          rw [fourier_add_arg]
          have := fourier_mul_fourier_neg k y
          linear_combination (-(fourier (-k) x : ℂ) * f (x + y)) * this
        simp only [h1]
        rw [integral_const_mul]
        congr 1
        exact integral_add_right_eq_self (fun x => (fourier (-k) x : ℂ) * f x) y
    _ = circleChar ν k * fourierCoeff f k := by
        rw [integral_mul_const]
        rfl

/-- Parseval's identity for an honest `L²` function on the circle. -/
theorem hasSum_sq_fourierCoeff_of_memLp {f : AddCircle T → ℂ}
    (hf : MemLp f 2 (haarAddCircle : Measure (AddCircle T))) :
    HasSum (fun i => ‖fourierCoeff f i‖ ^ 2) (∫ t, ‖f t‖ ^ 2 ∂haarAddCircle) := by
  have h := hasSum_sq_fourierCoeff (hf.toLp f)
  have hae := hf.coeFn_toLp
  have h1 : ∀ i, fourierCoeff (hf.toLp f) i = fourierCoeff f i := fun i =>
    congrFun (fourierCoeff_congr_ae hae) i
  have h2 : ∫ t, ‖(hf.toLp f) t‖ ^ 2 ∂haarAddCircle = ∫ t, ‖f t‖ ^ 2 ∂haarAddCircle :=
    integral_congr_ae (hae.mono fun t ht => by simp only [ht])
  simpa [h1, h2] using h

/-- **`L²` contraction from the Fourier–Stieltjes coefficients.** If `|ν̂(k)| ≤ ρ` for every
`k ≠ 0`, then `‖P f‖₂ ≤ ρ ‖f‖₂` for every mean-zero `f ∈ L²(𝕋)`. -/
theorem circle_l2ContractionBound (ν : Measure (AddCircle T)) [IsProbabilityMeasure ν] {ρ : ℝ}
    (hρ : ∀ k : ℤ, k ≠ 0 → ‖circleChar ν k‖ ≤ ρ) :
    AddL2ContractionBound (haarAddCircle : Measure (AddCircle T)) ν ρ := by
  intro f hf hmean
  have hPf := memLp_addMarkovOp haarAddCircle ν hf
  have hS1 := hasSum_sq_fourierCoeff_of_memLp hPf
  have hS2 := (hasSum_sq_fourierCoeff_of_memLp hf).mul_left (ρ ^ 2)
  refine hasSum_le (fun k => ?_) hS1 hS2
  rw [fourierCoeff_addMarkovOp ν (hf.integrable one_le_two) k, norm_mul, mul_pow]
  by_cases hk : k = 0
  · subst hk
    have : fourierCoeff f 0 = 0 := by
      simp [fourierCoeff, hmean]
    simp [this]
  · have h1 := hρ k hk
    have : ‖circleChar ν k‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    exact mul_le_mul_of_nonneg_right this (by positivity)

/-- Nontrivial characters have mean zero. -/
theorem integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x, (fourier k x : ℂ) ∂(haarAddCircle : Measure (AddCircle T)) = 0 :=
  integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hk hT.out)

theorem memLp_fourier (k : ℤ) :
    MemLp (fun x => (fourier k x : ℂ)) 2 (haarAddCircle : Measure (AddCircle T)) :=
  MemLp.of_bound (fourier k).continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (norm_fourier_apply k x).le)

/-- **Sharpness of the contraction bound.** Any `L²` contraction bound dominates every
`|ν̂(k)|`, `k ≠ 0`. -/
theorem circleChar_le_of_bound (ν : Measure (AddCircle T)) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (h : AddL2ContractionBound (haarAddCircle : Measure (AddCircle T)) ν ρ) {k : ℤ}
    (hk : k ≠ 0) : ‖circleChar ν k‖ ≤ ρ := by
  have hb := h _ (memLp_fourier k) (integral_fourier_eq_zero hk)
  rw [addMarkovOp_fourier] at hb
  simp only [norm_mul, norm_fourier_apply, mul_one, one_pow, integral_const, probReal_univ,
    smul_eq_mul, one_mul] at hb
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ0 two_ne_zero).mp hb

/-- **The second largest eigenvalue modulus on the circle.** If `|ν̂(k)| ≤ ρ` for all `k ≠ 0`
with equality for some `k₀ ≠ 0`, then `ρ` is the least `L²` contraction coefficient. -/
theorem circle_isLeast_contraction (ν : Measure (AddCircle T)) [IsProbabilityMeasure ν] {ρ : ℝ}
    (hρ : ∀ k : ℤ, k ≠ 0 → ‖circleChar ν k‖ ≤ ρ) {k₀ : ℤ} (hk₀ : k₀ ≠ 0)
    (heq : ‖circleChar ν k₀‖ = ρ) :
    IsLeast {ρ' : ℝ | 0 ≤ ρ' ∧
      AddL2ContractionBound (haarAddCircle : Measure (AddCircle T)) ν ρ'} ρ := by
  refine ⟨⟨heq ▸ norm_nonneg _, circle_l2ContractionBound ν hρ⟩, ?_⟩
  rintro ρ' ⟨h0, hb⟩
  exact heq ▸ circleChar_le_of_bound ν h0 hb hk₀

/-- `∫ (Re e_k)² = 1/2` for `k ≠ 0`. -/
theorem integral_fourier_re_sq {k : ℤ} (hk : k ≠ 0) :
    ∫ x, (fourier k x : ℂ).re ^ 2 ∂(haarAddCircle : Measure (AddCircle T)) = 1 / 2 := by
  have hkk : k + k ≠ 0 := by omega
  have hpt : ∀ x : AddCircle T,
      (fourier k x : ℂ).re ^ 2 = 1 / 2 + 1 / 2 * (fourier (k + k) x : ℂ).re := by
    intro x
    rw [fourier_add]
    have hn : ‖(fourier k x : ℂ)‖ = 1 := norm_fourier_apply k x
    have h1 : (fourier k x : ℂ).re ^ 2 + (fourier k x : ℂ).im ^ 2 = 1 := by
      have := Complex.sq_norm (fourier k x : ℂ)
      rw [hn, Complex.normSq_apply] at this
      nlinarith
    simp only [Complex.mul_re]
    nlinarith
  have hint : Integrable (fun x => (fourier (k + k) x : ℂ))
      (haarAddCircle : Measure (AddCircle T)) := (memLp_fourier (k + k)).integrable one_le_two
  have hre : ∫ x, (fourier (k + k) x : ℂ).re ∂(haarAddCircle : Measure (AddCircle T)) = 0 := by
    have := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at this
    rw [this, integral_fourier_eq_zero hkk]
    simp
  have h2 : Integrable (fun x => 1 / 2 * (fourier (k + k) x : ℂ).re)
      (haarAddCircle : Measure (AddCircle T)) :=
    ((memLp_fourier (k + k)).re.integrable one_le_two).const_mul _
  simp only [hpt]
  rw [integral_add (integrable_const _) h2, integral_const_mul, hre]
  simp

/-- **Spectral gap on the circle.** If `|ν̂(k)| ≤ ρ` for all `k ≠ 0` and `ν̂(k₀) = ρ` for some
`k₀ ≠ 0`, then the spectral gap of the walk is exactly `1 - ρ`. -/
theorem circle_isSpectralGap (ν : Measure (AddCircle T)) [IsProbabilityMeasure ν] {ρ : ℝ}
    (hρ : ∀ k : ℤ, k ≠ 0 → ‖circleChar ν k‖ ≤ ρ) {k₀ : ℤ} (hk₀ : k₀ ≠ 0)
    (heq : circleChar ν k₀ = (ρ : ℂ)) :
    IsAddSpectralGap (haarAddCircle : Measure (AddCircle T)) ν (1 - ρ) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ k₀ hk₀)
  refine ⟨(circle_l2ContractionBound ν hρ).addPoincareIneq hρ0, ?_⟩
  intro γ hγ
  -- the real eigenfunction `Re e_{k₀}`
  have hmemC := memLp_fourier (T := T) k₀
  have hintC : Integrable (fun x => (fourier k₀ x : ℂ))
      (haarAddCircle : Measure (AddCircle T)) := hmemC.integrable one_le_two
  have hmem : MemLp (fun x => (fourier k₀ x : ℂ).re) 2
      (haarAddCircle : Measure (AddCircle T)) := hmemC.re
  have hmean : ∫ x, (fourier k₀ x : ℂ).re ∂(haarAddCircle : Measure (AddCircle T)) = 0 := by
    have := Complex.reCLM.integral_comp_comm hintC
    simp only [Complex.reCLM_apply] at this
    rw [this, integral_fourier_eq_zero hk₀]
    simp
  have hpos : 0 < ∫ x, (fourier k₀ x : ℂ).re ^ 2 ∂(haarAddCircle : Measure (AddCircle T)) := by
    rw [integral_fourier_re_sq hk₀]
    norm_num
  have heig : addMarkovOp ν (fun x => (fourier k₀ x : ℂ).re)
      = fun x => ρ * (fourier k₀ x : ℂ).re := by
    funext x
    have hC := congrFun (addMarkovOp_fourier ν k₀) x
    simp only [addMarkovOp] at hC ⊢
    have hint : Integrable (fun y => (fourier k₀ (x + y) : ℂ)) ν :=
      Integrable.of_bound ((fourier k₀).continuous.comp
        (continuous_const.add continuous_id)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun y => (norm_fourier_apply k₀ _).le)
    have := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at this
    rw [this, hC, heq, Complex.re_ofReal_mul]
  exact hγ.le_of_eigenfunction hmem hmean hpos heig

end Circle

end SOnMCMC

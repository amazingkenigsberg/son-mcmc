import SOnMCMC.CircleSampler

/-!
# The `SO(2)` spectral gap to second order, and geometric `L²` convergence

Paper: Section 4.4.

* `integral_pow_four_gaussianReal`: the fourth moment of `N(0, v)` is `3 v²`;
* `abs_one_sub_gaussLam_sub_le`: the spectral gap `γ = 1 - λ₁` of the `SO(2)` sampler with
  proposal variance `v = σ²` satisfies `|γ - σ²/2| ≤ (3/2) σ⁴`;
* `L2ContractionBound.iterate`: an `L²` contraction bound `ρ` gives `‖Pᵗ f‖₂ ≤ ρᵗ ‖f‖₂` on
  mean-zero functions;
* `gauss_iterate_bound`: for the `SO(2)` sampler, `‖Pᵗ f‖₂ ≤ λ₁ᵗ ‖f‖₂`.
-/

open MeasureTheory Real ProbabilityTheory
open scoped NNReal ENNReal

namespace SOnMCMC

/-! ### Moments of the Gaussian -/

/-- All power moments of the centred Gaussian are finite. -/
theorem integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun a : ℝ => a ^ k) (gaussianReal 0 v) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · have h : MemLp (id : ℝ → ℝ) (k : ℕ) (gaussianReal 0 v) := by
      have := memLp_id_gaussianReal (μ := 0) (v := v) (k : ℝ≥0)
      simpa using this
    have h2 := h.integrable_norm_pow hk.ne'
    have hm : AEStronglyMeasurable (fun a : ℝ => a ^ k) (gaussianReal 0 v) :=
      (measurable_id.pow_const k).aestronglyMeasurable
    refine (integrable_norm_iff hm).mp ?_
    simpa [norm_pow] using h2

/-- Integrability against the Gaussian law is integrability against Lebesgue measure after
multiplying by the density. -/
theorem integrable_pdf_mul {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable (fun x => gaussianPDFReal 0 v x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 v) (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [toReal_gaussianPDF] using hg

theorem gaussianPDFReal_zero_eq (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x = (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v)) := by
  simp [gaussianPDFReal]

theorem gaussianPDFDeriv_eq (v : ℝ≥0) (x : ℝ) :
    gaussianPDFDeriv v x = gaussianPDFReal 0 v x * (-x / v) := by
  rw [gaussianPDFDeriv, gaussianPDFReal_zero_eq]

/-- **Fourth moment of the centred Gaussian:** `E[a⁴] = 3 v²`. -/
theorem integral_pow_four_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ a, a ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h2 := integrable_pdf_mul hv (integrable_pow_gaussianReal v 2)
  have h3 := integrable_pdf_mul hv (integrable_pow_gaussianReal v 3)
  have h4 := integrable_pdf_mul hv (integrable_pow_gaussianReal v 4)
  -- integration by parts with `u = x³`, `v = φ`
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ 3) (u' := fun x : ℝ => 3 * x ^ 2)
    (v := gaussianPDFReal 0 v) (v' := gaussianPDFDeriv v)
    (fun x _ => by simpa using hasDerivAt_pow 3 x)
    (fun x _ => hasDerivAt_gaussianPDFReal hv x)
    (by
      have : (fun x : ℝ => x ^ 3) * gaussianPDFDeriv v
          = fun x => (-(1 / (v : ℝ))) * (gaussianPDFReal 0 v x * x ^ 4) := by
        funext x
        simp only [Pi.mul_apply, gaussianPDFDeriv_eq]
        field_simp
      rw [this]
      exact h4.const_mul _)
    (by
      have : (fun x : ℝ => 3 * x ^ 2) * gaussianPDFReal 0 v
          = fun x => 3 * (gaussianPDFReal 0 v x * x ^ 2) := by
        funext x
        simp only [Pi.mul_apply]
        ring
      rw [this]
      exact h2.const_mul _)
    (by
      have : (fun x : ℝ => x ^ 3) * gaussianPDFReal 0 v
          = fun x => gaussianPDFReal 0 v x * x ^ 3 := by
        funext x
        simp only [Pi.mul_apply]
        ring
      rw [this]
      exact h3)
  have hL : ∫ x, x ^ 3 * gaussianPDFDeriv v x
      = -(1 / (v : ℝ)) * ∫ x, gaussianPDFReal 0 v x * x ^ 4 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [gaussianPDFDeriv_eq]
    field_simp
  have hR : ∫ x, 3 * x ^ 2 * gaussianPDFReal 0 v x
      = 3 * ∫ x, gaussianPDFReal 0 v x * x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [hL, hR] at hparts
  have hsq : ∫ x, gaussianPDFReal 0 v x * x ^ 2 = v := by
    have := integral_sq_gaussianReal v
    rwa [integral_gaussianReal_eq_integral_smul hv] at this
  rw [hsq] at hparts
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have : (∫ x, gaussianPDFReal 0 v x * x ^ 4) = 3 * (v : ℝ) ^ 2 := by
    field_simp at hparts
    linarith
  exact this

/-! ### Second-order bounds on the one-step displacement -/

theorem one_sub_sqrt_le_quadratic {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    1 - √(1 - x) ≤ x / 2 + x ^ 2 / 2 := by
  have hnn : 0 ≤ 1 - x / 2 - x ^ 2 / 2 := by nlinarith
  have h : 1 - x / 2 - x ^ 2 / 2 ≤ √(1 - x) := by
    rw [show (1 - x / 2 - x ^ 2 / 2) = √((1 - x / 2 - x ^ 2 / 2) ^ 2) from
      (Real.sqrt_sq hnn).symm]
    apply Real.sqrt_le_sqrt
    have h3 : 0 ≤ x ^ 2 * (3 / 4 - x / 2 - x ^ 2 / 4) := by
      apply mul_nonneg (sq_nonneg x)
      nlinarith
    nlinarith
  linarith

theorem one_sub_cos_stepAngle_le_quartic (a : ℝ) :
    1 - cos (stepAngle a) ≤ a ^ 2 / 2 + a ^ 4 / 2 := by
  rw [one_sub_cos_stepAngle]
  split_ifs with h
  · have h1 : a ^ 2 ≤ 1 := by
      have := abs_le.mp h
      nlinarith
    have := one_sub_sqrt_le_quadratic (sq_nonneg a) h1
    have e : (a ^ 2) ^ 2 = a ^ 4 := by ring
    rw [e] at this
    exact this
  · positivity

theorem one_sub_cos_stepAngle_ge_quartic (a : ℝ) :
    a ^ 2 / 2 - a ^ 4 / 2 ≤ 1 - cos (stepAngle a) := by
  rw [one_sub_cos_stepAngle]
  split_ifs with h
  · have h1 : a ^ 2 ≤ 1 := by
      have := abs_le.mp h
      nlinarith
    have := half_le_one_sub_sqrt (sq_nonneg a) h1
    have : 0 ≤ a ^ 4 / 2 := by positivity
    linarith
  · have h1 : 1 < a ^ 2 := by
      have h2 : 1 < |a| := not_le.mp h
      have h3 : |a| ^ 2 = a ^ 2 := sq_abs a
      nlinarith
    have e : a ^ 4 = a ^ 2 * a ^ 2 := by ring
    rw [e]
    nlinarith

/-- **Theorem (the `SO(2)` spectral gap to second order).** For Gaussian tangent proposals of
variance `v = σ²`, the spectral gap `γ = 1 - λ₁` satisfies `|γ - σ²/2| ≤ (3/2) σ⁴`. -/
theorem abs_one_sub_gaussLam_sub_le {v : ℝ≥0} (hv : v ≠ 0) :
    |1 - gaussLam v - v / 2| ≤ 3 / 2 * (v : ℝ) ^ 2 := by
  have hi := integrable_cos_mul_stepAngle (gaussianReal 0 v) 1
  simp only [one_mul] at hi
  have hgap : ∫ a, (1 - cos (stepAngle a)) ∂(gaussianReal 0 v) = 1 - gaussLam v := by
    rw [integral_sub (integrable_const _) hi]
    simp [gaussLam]
  have hI : Integrable (fun a => 1 - cos (stepAngle a)) (gaussianReal 0 v) :=
    (integrable_const _).sub hi
  have h2 := integrable_pow_gaussianReal v 2
  have h4 := integrable_pow_gaussianReal v 4
  have hm2 := integral_sq_gaussianReal v
  have hm4 := integral_pow_four_gaussianReal hv
  have hup : 1 - gaussLam v ≤ v / 2 + 3 * (v : ℝ) ^ 2 / 2 := by
    rw [← hgap]
    calc ∫ a, (1 - cos (stepAngle a)) ∂(gaussianReal 0 v)
        ≤ ∫ a, (a ^ 2 / 2 + a ^ 4 / 2) ∂(gaussianReal 0 v) :=
          integral_mono hI ((h2.div_const 2).add (h4.div_const 2))
            one_sub_cos_stepAngle_le_quartic
      _ = v / 2 + 3 * (v : ℝ) ^ 2 / 2 := by
          rw [integral_add (h2.div_const 2) (h4.div_const 2), integral_div, integral_div, hm2,
            hm4]
  have hlo : v / 2 - 3 * (v : ℝ) ^ 2 / 2 ≤ 1 - gaussLam v := by
    rw [← hgap]
    calc (v : ℝ) / 2 - 3 * (v : ℝ) ^ 2 / 2
        = ∫ a, (a ^ 2 / 2 - a ^ 4 / 2) ∂(gaussianReal 0 v) := by
          rw [integral_sub (h2.div_const 2) (h4.div_const 2), integral_div, integral_div, hm2,
            hm4]
      _ ≤ ∫ a, (1 - cos (stepAngle a)) ∂(gaussianReal 0 v) :=
          integral_mono ((h2.div_const 2).sub (h4.div_const 2)) hI
            one_sub_cos_stepAngle_ge_quartic
  rw [abs_le]
  constructor <;> linarith

/-! ### Geometric convergence of iterates -/

section Iterate

variable {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd₂ G]

/-- **Geometric `L²` convergence.** If `‖P f‖₂ ≤ ρ ‖f‖₂` on mean-zero functions, then
`‖Pᵗ f‖₂ ≤ ρᵗ ‖f‖₂` for every mean-zero `f ∈ L²` and every `t`. -/
theorem AddL2ContractionBound.iterate {m ν : Measure G} [IsProbabilityMeasure m]
    [IsProbabilityMeasure ν] [m.IsAddRightInvariant] {ρ : ℝ}
    (hρ : AddL2ContractionBound m ν ρ) {f : G → ℂ} (hf : MemLp f 2 m)
    (hmean : ∫ x, f x ∂m = 0) (t : ℕ) :
    MemLp ((addMarkovOp ν)^[t] f) 2 m ∧ ∫ x, (addMarkovOp ν)^[t] f x ∂m = 0 ∧
      ∫ x, ‖(addMarkovOp ν)^[t] f x‖ ^ 2 ∂m ≤ (ρ ^ 2) ^ t * ∫ x, ‖f x‖ ^ 2 ∂m := by
  induction t with
  | zero => exact ⟨hf, hmean, by simp⟩
  | succ t ih =>
    obtain ⟨hmem, hm0, hb⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨memLp_addMarkovOp m ν hmem, ?_, ?_⟩
    · rw [integral_addMarkovOp m ν (hmem.integrable one_le_two), hm0]
    · calc ∫ x, ‖addMarkovOp ν ((addMarkovOp ν)^[t] f) x‖ ^ 2 ∂m
          ≤ ρ ^ 2 * ∫ x, ‖(addMarkovOp ν)^[t] f x‖ ^ 2 ∂m := hρ _ hmem hm0
        _ ≤ ρ ^ 2 * ((ρ ^ 2) ^ t * ∫ x, ‖f x‖ ^ 2 ∂m) :=
            mul_le_mul_of_nonneg_left hb (sq_nonneg ρ)
        _ = (ρ ^ 2) ^ (t + 1) * ∫ x, ‖f x‖ ^ 2 ∂m := by ring

end Iterate

/-- **Corollary (convergence of the `SO(2)` sampler).** For every mean-zero `f ∈ L²(𝕋)` and every
`t`, `‖Pᵗ f‖₂² ≤ λ₁^{2t} ‖f‖₂²`. -/
theorem gauss_iterate_bound {v : ℝ≥0} (hv : v ≠ 0) {f : AddCircle (2 * π) → ℂ}
    (hf : MemLp f 2 (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))))
    (hmean : ∫ x, f x ∂(AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) = 0) (t : ℕ) :
    ∫ x, ‖(addMarkovOp (gaussStep v))^[t] f x‖ ^ 2
        ∂(AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))
      ≤ (gaussLam v ^ 2) ^ t
        * ∫ x, ‖f x‖ ^ 2 ∂(AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) :=
  ((gauss_isLeast_contraction hv).1.2.iterate hf hmean t).2.2

end SOnMCMC

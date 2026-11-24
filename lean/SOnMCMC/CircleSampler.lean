import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Gaussian.Real
import SOnMCMC.Circle

/-!
# The tangent-space sampler on `SO(2)`

Paper: Sections 4.2–4.4.

At a point of the circle, the sampler proposes a tangent step with signed length `a`, and
projects back to the circle along the normal direction.  The projection exists iff `|a| ≤ 1`,
and then the point moves by the angle `arcsin a`; otherwise the proposal is rejected.  The
step distribution on `𝕋 = ℝ / 2πℤ` is therefore the law of `stepAngle a`.

Main results:

* `abs_sin_nat_mul_le`: `|sin (k t)| ≤ k |sin t|`;
* `unimodal_integral_nonneg`: for an even `C¹` density `φ` that is non-increasing on `[0,1]`,
  `∫ (cos θ(a) ± cos (k θ(a))) φ(a) da ≥ 0`;
* `gauss_char_le`: for Gaussian proposals, `|ν̂(k)| ≤ ν̂(1)` for every `k ≠ 0`;
* `gauss_isSpectralGap`, `gauss_isLeast_contraction`: the spectral gap of the sampler is exactly
  `1 - ν̂(1)`, and `ν̂(1)` is the `L²` contraction coefficient;
* `one_sub_gaussLam_le`, `one_sub_gaussLam_ge`: `½ E[a²; |a| ≤ 1] ≤ gap ≤ σ²`.
-/

open MeasureTheory Set Real ProbabilityTheory
open scoped Real NNReal

namespace SOnMCMC

/-! ### An elementary trigonometric inequality -/

/-- `|sin (k t)| ≤ k |sin t|` for every natural number `k`. -/
theorem abs_sin_nat_mul_le (k : ℕ) (t : ℝ) : |sin (k * t)| ≤ k * |sin t| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : sin ((k + 1 : ℕ) * t) = sin (k * t) * cos t + cos (k * t) * sin t := by
      push_cast
      rw [add_mul, one_mul, sin_add]
    rw [h]
    calc |sin (k * t) * cos t + cos (k * t) * sin t|
        ≤ |sin (k * t) * cos t| + |cos (k * t) * sin t| := abs_add_le _ _
      _ ≤ |sin (k * t)| + |sin t| := by
          rw [abs_mul, abs_mul]
          have h1 := abs_cos_le_one t
          have h2 := abs_cos_le_one (k * t)
          have h3 := abs_nonneg (sin (k * t))
          have h4 := abs_nonneg (sin t)
          have h5 := abs_nonneg (cos t)
          have h6 := abs_nonneg (cos (k * t))
          nlinarith
      _ ≤ ((k + 1 : ℕ) : ℝ) * |sin t| := by
          push_cast
          linarith

/-- `sin t + ε sin (k t) / k ≥ 0` on `[0, π]` when `|ε| ≤ 1`. -/
theorem sin_add_mul_sin_div_nonneg {k : ℕ} (hk : k ≠ 0) {ε : ℝ} (hε : |ε| ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htπ : t ≤ π) : 0 ≤ sin t + ε * (sin (k * t) / k) := by
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht0 htπ
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have h1 := abs_sin_nat_mul_le k t
  rw [abs_of_nonneg hs] at h1
  have h2 : |sin (k * t) / k| ≤ sin t := by
    rw [abs_div, abs_of_pos hk', div_le_iff₀ hk']
    linarith
  have h3 : |ε * (sin (k * t) / k)| ≤ sin t := by
    rw [abs_mul]
    calc |ε| * |sin (k * t) / k| ≤ 1 * sin t := mul_le_mul hε h2 (abs_nonneg _) zero_le_one
      _ = sin t := one_mul _
  linarith [neg_abs_le (ε * (sin (k * t) / k))]

/-! ### The key integral inequality -/

/-- Integration by parts on `[0, π/2]` against the weight `φ (sin t) cos t`. -/
theorem core_integral_nonneg {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ'c : Continuous φ') (hφ0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ φ x)
    (hφ' : ∀ x ∈ Icc (0 : ℝ) 1, φ' x ≤ 0) {k : ℕ} (hk : k ≠ 0) {ε : ℝ} (hε : |ε| ≤ 1) :
    0 ≤ ∫ t in (0 : ℝ)..(π / 2), (φ (sin t) * cos t) * (cos t + ε * cos (k * t)) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hwd : ∀ t, HasDerivAt (fun t => φ (sin t) * cos t)
      (φ' (sin t) * cos t * cos t + φ (sin t) * (-sin t)) t := fun t =>
    ((hφ (sin t)).comp t (hasDerivAt_sin t)).mul (hasDerivAt_cos t)
  have hGd : ∀ t, HasDerivAt (fun t => sin t + ε * (sin (k * t) / k))
      (cos t + ε * cos (k * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => sin (k * t)) (cos (k * t) * k) t := by
      have := ((hasDerivAt_id t).const_mul (k : ℝ)).sin
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => sin (k * t) / k) (cos (k * t)) t :=
      (h1.div_const (k : ℝ)).congr_deriv (mul_div_cancel_right₀ _ hk')
    exact (hasDerivAt_sin t).add (h2.const_mul ε)
  have hw'c : Continuous (fun t => φ' (sin t) * cos t * cos t + φ (sin t) * (-sin t)) := by
    fun_prop
  have hG'c : Continuous (fun t => cos t + ε * cos (k * t)) := by fun_prop
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := π / 2)
    (fun x _ => hwd x) (fun x _ => hGd x) (hw'c.intervalIntegrable _ _)
    (hG'c.intervalIntegrable _ _)
  rw [key]
  simp only [cos_pi_div_two, mul_zero, zero_mul, sin_zero, zero_div, add_zero, sub_zero,
    zero_sub]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_nonneg (by positivity)
  intro t ht
  have htπ : t ≤ π := by linarith [ht.2, pi_pos]
  have hs0 : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 htπ
  have hs1 : sin t ≤ 1 := sin_le_one t
  have hGt : 0 ≤ sin t + ε * (sin (k * t) / k) := sin_add_mul_sin_div_nonneg hk hε ht.1 htπ
  have hw't : φ' (sin t) * cos t * cos t + φ (sin t) * (-sin t) ≤ 0 := by
    have h1 := hφ' (sin t) ⟨hs0, hs1⟩
    have h2 := hφ0 (sin t) ⟨hs0, hs1⟩
    have h3 : φ' (sin t) * cos t * cos t ≤ 0 := by
      have : φ' (sin t) * cos t * cos t = φ' (sin t) * (cos t * cos t) := by ring
      rw [this]
      exact mul_nonpos_of_nonpos_of_nonneg h1 (mul_self_nonneg _)
    have h4 : φ (sin t) * (-sin t) ≤ 0 := by
      have := mul_nonneg h2 hs0
      linarith
    linarith
  have := mul_nonneg (neg_nonneg.mpr hw't) hGt
  linarith

/-- The substitution `a = sin t` on `[0, 1]`. -/
theorem integral_zero_one_eq_integral_sin (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    ∫ a in (0 : ℝ)..1, ψ a = ∫ t in (0 : ℝ)..(π / 2), ψ (sin t) * cos t := by
  have := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π / 2) (f := sin) (f' := cos)
    (g := ψ) (fun x _ => hasDerivAt_sin x) continuous_cos.continuousOn hψ
  simpa using this.symm

/-- The inequality on `[0, 1]` in the tangent coordinate. -/
theorem integral_zero_one_nonneg {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ'c : Continuous φ') (hφ0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ φ x)
    (hφ' : ∀ x ∈ Icc (0 : ℝ) 1, φ' x ≤ 0) {k : ℕ} (hk : k ≠ 0) {ε : ℝ} (hε : |ε| ≤ 1) :
    0 ≤ ∫ a in (0 : ℝ)..1, (cos (arcsin a) + ε * cos (k * arcsin a)) * φ a := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hψ : Continuous (fun a => (cos (arcsin a) + ε * cos (k * arcsin a)) * φ a) := by
    have := continuous_arcsin
    fun_prop
  rw [integral_zero_one_eq_integral_sin _ hψ]
  have hcongr : ∫ t in (0 : ℝ)..(π / 2),
        (cos (arcsin (sin t)) + ε * cos (k * arcsin (sin t))) * φ (sin t) * cos t
      = ∫ t in (0 : ℝ)..(π / 2), (φ (sin t) * cos t) * (cos t + ε * cos (k * t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by positivity)] at ht
    have : arcsin (sin t) = t := arcsin_sin (by linarith [ht.1, pi_pos]) ht.2
    simp only [this]
    ring
  rw [hcongr]
  exact core_integral_nonneg hφ hφ'c hφ0 hφ' hk hε

/-! ### The step angle -/

/-- The angle by which the sampler moves when the tangent proposal has signed length `a`:
`arcsin a` if the projection exists (`|a| ≤ 1`), and `0` (rejection) otherwise. -/
noncomputable def stepAngle (a : ℝ) : ℝ := if |a| ≤ 1 then arcsin a else 0

theorem stepAngle_neg (a : ℝ) : stepAngle (-a) = -stepAngle a := by
  simp only [stepAngle, abs_neg, arcsin_neg]
  split_ifs <;> simp

theorem stepAngle_of_abs_le {a : ℝ} (h : |a| ≤ 1) : stepAngle a = arcsin a := by
  simp [stepAngle, h]

theorem stepAngle_of_lt {a : ℝ} (h : 1 < |a|) : stepAngle a = 0 := by
  simp [stepAngle, not_le.mpr h]

theorem measurable_stepAngle : Measurable stepAngle :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    measurable_arcsin measurable_const

/-- `cos (stepAngle a) = √(1 - a²)` on acceptance and `1` on rejection. -/
theorem cos_stepAngle (a : ℝ) :
    cos (stepAngle a) = if |a| ≤ 1 then √(1 - a ^ 2) else 1 := by
  by_cases h : |a| ≤ 1
  · simp [stepAngle, h, cos_arcsin]
  · simp [stepAngle, h]

/-- **Domination of all Fourier modes by the first, for unimodal proposal densities.**
Let `φ` be an even, nonnegative, integrable `C¹` function that is non-increasing on `[0, 1]`.
Then for every `k ≥ 1` and `|ε| ≤ 1`,
`∫ (cos θ(a) + ε cos (k θ(a))) φ(a) da ≥ 0`, where `θ = stepAngle`. -/
theorem unimodal_integral_nonneg {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ'c : Continuous φ') (hφnn : ∀ x, 0 ≤ φ x) (hφ' : ∀ x ∈ Icc (0 : ℝ) 1, φ' x ≤ 0)
    (heven : ∀ x, φ (-x) = φ x) (hint : Integrable φ) {k : ℕ} (hk : k ≠ 0) {ε : ℝ}
    (hε : |ε| ≤ 1) :
    0 ≤ ∫ a, (cos (stepAngle a) + ε * cos (k * stepAngle a)) * φ a := by
  set f : ℝ → ℝ := fun a => (cos (stepAngle a) + ε * cos (k * stepAngle a)) * φ a with hf
  have hε' := abs_le.mp hε
  have hfeven : ∀ a, f |a| = f a := by
    intro a
    rcases abs_choice a with h | h
    · rw [h]
    · rw [h]
      simp only [hf, stepAngle_neg, heven, mul_neg, cos_neg]
  have hfint : Integrable f := by
    refine hint.bdd_mul (c := 2) ?_ ?_
    · have := measurable_stepAngle
      exact (by fun_prop : Measurable fun a => cos (stepAngle a) + ε * cos (k * stepAngle a))
        |>.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun a => ?_
      rw [Real.norm_eq_abs]
      calc |cos (stepAngle a) + ε * cos (k * stepAngle a)|
          ≤ |cos (stepAngle a)| + |ε * cos (k * stepAngle a)| := abs_add_le _ _
        _ ≤ 1 + 1 := by
            refine add_le_add (abs_cos_le_one _) ?_
            rw [abs_mul]
            exact mul_le_one₀ hε (abs_nonneg _) (abs_cos_le_one _)
        _ = 2 := by norm_num
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx')
  have hsplit : ∫ a in Ioi (0 : ℝ), f a
      = (∫ a in Ioc (0 : ℝ) 1, f a) + ∫ a in Ioi (1 : ℝ), f a := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
    exact setIntegral_union hdisj measurableSet_Ioi hfint.integrableOn hfint.integrableOn
  have htail : 0 ≤ ∫ a in Ioi (1 : ℝ), f a := by
    refine setIntegral_nonneg measurableSet_Ioi fun a ha => ?_
    have ha' : 1 < |a| := lt_of_lt_of_le ha (le_abs_self a)
    simp only [hf, stepAngle_of_lt ha', mul_zero, cos_zero, mul_one]
    exact mul_nonneg (by linarith [hε'.1]) (hφnn a)
  have hmain : 0 ≤ ∫ a in Ioc (0 : ℝ) 1, f a := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have hcongr : ∫ a in (0 : ℝ)..1, f a
        = ∫ a in (0 : ℝ)..1, (cos (arcsin a) + ε * cos (k * arcsin a)) * φ a := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le zero_le_one] at ha
      have : |a| ≤ 1 := by rw [abs_of_nonneg ha.1]; exact ha.2
      simp only [hf, stepAngle_of_abs_le this]
    rw [hcongr]
    exact integral_zero_one_nonneg hφ hφ'c (fun x _ => hφnn x) hφ' hk hε
  calc (0 : ℝ) ≤ 2 * ∫ a in Ioi (0 : ℝ), f a := by rw [hsplit]; linarith
    _ = ∫ a, f |a| := integral_comp_abs.symm
    _ = ∫ a, f a := by simp only [hfeven]

/-! ### The step distribution on the circle -/

instance instFactTwoPiPos : Fact ((0 : ℝ) < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The step distribution on `𝕋 = ℝ / 2πℤ` induced by a law `γ` of the tangent coordinate. -/
noncomputable def circleStep (γ : Measure ℝ) : Measure (AddCircle (2 * π)) :=
  γ.map (fun a => ((stepAngle a : ℝ) : AddCircle (2 * π)))

theorem measurable_coe_stepAngle :
    Measurable (fun a => ((stepAngle a : ℝ) : AddCircle (2 * π))) :=
  (AddCircle.measurable_mk').comp measurable_stepAngle

instance (γ : Measure ℝ) [IsProbabilityMeasure γ] : IsProbabilityMeasure (circleStep γ) :=
  Measure.isProbabilityMeasure_map measurable_coe_stepAngle.aemeasurable

/-- On `ℝ / 2πℤ`, `e_k(x) = cos (k x) + i sin (k x)`. -/
theorem fourier_coe_two_pi (k : ℤ) (x : ℝ) :
    (fourier k ((x : ℝ) : AddCircle (2 * π)) : ℂ)
      = ((cos (k * x) : ℝ) : ℂ) + ((sin (k * x) : ℝ) : ℂ) * Complex.I := by
  rw [fourier_coe_apply]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have : (2 * π * Complex.I * k * x / ((2 * π : ℝ) : ℂ) : ℂ) = ((k * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- For a symmetric proposal law, the Fourier–Stieltjes coefficients of the step distribution
are real: `ν̂(k) = E[cos (k θ(a))]`. -/
theorem circleChar_circleStep (γ : Measure ℝ) [IsProbabilityMeasure γ]
    (hsymm : γ.map (fun x => -x) = γ) (k : ℤ) :
    circleChar (circleStep γ) k = ((∫ a, cos (k * stepAngle a) ∂γ : ℝ) : ℂ) := by
  have hms := measurable_stepAngle
  rw [circleChar, circleStep, integral_map measurable_coe_stepAngle.aemeasurable
    (fourier k).continuous.aestronglyMeasurable]
  simp only [fourier_coe_two_pi]
  have hc : Integrable (fun a => cos (k * stepAngle a)) γ :=
    Integrable.of_bound (by fun_prop : Measurable fun a => cos (k * stepAngle a)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun a => abs_cos_le_one _)
  have hs : Integrable (fun a => sin (k * stepAngle a)) γ :=
    Integrable.of_bound (by fun_prop : Measurable fun a => sin (k * stepAngle a)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun a => abs_sin_le_one _)
  have hzero : ∫ a, sin (k * stepAngle a) ∂γ = 0 := by
    have hm : AEStronglyMeasurable (fun a => sin (k * stepAngle a))
        (Measure.map (fun x => -x) γ) := by
      rw [hsymm]
      exact hs.aestronglyMeasurable
    have h1 := integral_map (μ := γ) (φ := fun x => -x) measurable_neg.aemeasurable hm
    rw [hsymm] at h1
    simp only [stepAngle_neg, mul_neg, sin_neg] at h1
    rw [integral_neg] at h1
    linarith
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, hzero]
  simp

/-! ### Gaussian proposals -/

/-- The step distribution of the tangent-space sampler on `SO(2) ≅ ℝ / 2πℤ` with `N(0, v)`
tangent proposals. -/
noncomputable def gaussStep (v : ℝ≥0) : Measure (AddCircle (2 * π)) :=
  circleStep (gaussianReal 0 v)

instance (v : ℝ≥0) : IsProbabilityMeasure (gaussStep v) := by
  unfold gaussStep
  infer_instance

/-- The leading nontrivial eigenvalue `λ₁ = E[cos θ(a)]`, `a ∼ N(0, v)`. -/
noncomputable def gaussLam (v : ℝ≥0) : ℝ := ∫ a, cos (stepAngle a) ∂(gaussianReal 0 v)

theorem gaussianReal_zero_symm (v : ℝ≥0) :
    (gaussianReal 0 v).map (fun x => -x) = gaussianReal 0 v := by
  rw [gaussianReal_map_neg, neg_zero]

theorem circleChar_gaussStep (v : ℝ≥0) (k : ℤ) :
    circleChar (gaussStep v) k
      = ((∫ a, cos (k * stepAngle a) ∂(gaussianReal 0 v) : ℝ) : ℂ) :=
  circleChar_circleStep _ (gaussianReal_zero_symm v) k

theorem circleChar_gaussStep_one (v : ℝ≥0) : circleChar (gaussStep v) 1 = (gaussLam v : ℂ) := by
  have := circleChar_gaussStep v 1
  simpa [gaussLam] using this

/-- The derivative of the centred Gaussian density, `-(x/v) φ(x)`, written out. -/
noncomputable def gaussianPDFDeriv (v : ℝ≥0) (x : ℝ) : ℝ :=
  (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v)) * (-x / v)

/-- The Gaussian density is differentiable, with derivative `-(x/v) φ(x)`. -/
theorem hasDerivAt_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (gaussianPDFDeriv v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h0 : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * (v : ℝ))) (-x / v) x := by
    have h := ((hasDerivAt_pow 2 x).neg).div_const (2 * (v : ℝ))
    refine h.congr_deriv ?_
    norm_num
    field_simp
  have h2 := (h0.exp).const_mul ((√(2 * π * v))⁻¹)
  have e : gaussianPDFReal 0 v
      = fun y : ℝ => (√(2 * π * v))⁻¹ * rexp (-y ^ 2 / (2 * v)) := by
    rw [gaussianPDFReal_def]
    funext y
    simp
  rw [e]
  refine h2.congr_deriv ?_
  simp only [gaussianPDFDeriv]
  ring

theorem continuous_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) : Continuous (gaussianPDFReal 0 v) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gaussianPDFReal hv x).continuousAt

/-- The key inequality for Gaussian proposals. -/
theorem gauss_integral_nonneg {v : ℝ≥0} (hv : v ≠ 0) {k : ℕ} (hk : k ≠ 0) {ε : ℝ}
    (hε : |ε| ≤ 1) :
    0 ≤ ∫ a, (cos (stepAngle a) + ε * cos (k * stepAngle a)) ∂(gaussianReal 0 v) := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.mpr hv
  have := unimodal_integral_nonneg (φ := gaussianPDFReal 0 v)
    (φ' := gaussianPDFDeriv v) (hasDerivAt_gaussianPDFReal hv)
    (by unfold gaussianPDFDeriv; fun_prop) (gaussianPDFReal_nonneg 0 v)
    (fun x hx => by
      have h1 : 0 ≤ (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v)) := by positivity
      have h2 : -x / (v : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hx.1]) hvpos.le
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2)
    (fun x => by simp [gaussianPDFReal]) (integrable_gaussianPDFReal 0 v) hk hε
  simpa [mul_comm] using this

theorem integrable_cos_mul_stepAngle (γ : Measure ℝ) [IsFiniteMeasure γ] (c : ℝ) :
    Integrable (fun a => cos (c * stepAngle a)) γ := by
  have := measurable_stepAngle
  exact Integrable.of_bound (by fun_prop : Measurable fun a => cos (c * stepAngle a)).aestronglyMeasurable
    1 (Filter.Eventually.of_forall fun a => abs_cos_le_one _)

/-- **For Gaussian proposals the first Fourier mode dominates:** `|ν̂(k)| ≤ ν̂(1)` for `k ≠ 0`. -/
theorem gauss_char_le {v : ℝ≥0} (hv : v ≠ 0) {k : ℤ} (hk : k ≠ 0) :
    ‖circleChar (gaussStep v) k‖ ≤ gaussLam v := by
  rw [circleChar_gaussStep, Complex.norm_real, Real.norm_eq_abs]
  -- reduce to a natural frequency
  have hnat : ∫ a, cos (k * stepAngle a) ∂(gaussianReal 0 v)
      = ∫ a, cos ((k.natAbs : ℝ) * stepAngle a) ∂(gaussianReal 0 v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rcases Int.natAbs_eq k with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      simp
  rw [hnat]
  have hk' : k.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hk
  have hi1 := integrable_cos_mul_stepAngle (gaussianReal 0 v) 1
  simp only [one_mul] at hi1
  have hik := integrable_cos_mul_stepAngle (gaussianReal 0 v) (k.natAbs : ℝ)
  have hplus := gauss_integral_nonneg hv hk' (ε := 1) (by simp)
  have hminus := gauss_integral_nonneg hv hk' (ε := -1) (by simp)
  simp only [one_mul] at hplus
  simp only [neg_one_mul, ← sub_eq_add_neg] at hminus
  rw [integral_add hi1 hik] at hplus
  rw [integral_sub hi1 hik] at hminus
  rw [abs_le]
  unfold gaussLam
  constructor <;> linarith

/-- `λ₁ ≥ 0`. -/
theorem gaussLam_nonneg {v : ℝ≥0} (hv : v ≠ 0) : 0 ≤ gaussLam v :=
  (norm_nonneg _).trans (gauss_char_le hv one_ne_zero)

/-- **Theorem (spectral gap of the `SO(2)` sampler).** For Gaussian tangent proposals of
variance `v > 0`, the spectral gap of the sampler is exactly `1 - λ₁` with
`λ₁ = E[cos θ(a)]`. -/
theorem gauss_isSpectralGap {v : ℝ≥0} (hv : v ≠ 0) :
    IsAddSpectralGap (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) (gaussStep v)
      (1 - gaussLam v) :=
  circle_isSpectralGap (gaussStep v) (fun _ hk => gauss_char_le hv hk) one_ne_zero
    (circleChar_gaussStep_one v)

/-- **Theorem (`L²` convergence rate of the `SO(2)` sampler).** `λ₁` is the least `L²`
contraction coefficient on mean-zero functions: `‖P f‖₂ ≤ λ₁ ‖f‖₂`, and no smaller constant
works. -/
theorem gauss_isLeast_contraction {v : ℝ≥0} (hv : v ≠ 0) :
    IsLeast {ρ : ℝ | 0 ≤ ρ ∧ AddL2ContractionBound
      (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) (gaussStep v) ρ} (gaussLam v) := by
  refine circle_isLeast_contraction (gaussStep v) (fun _ hk => gauss_char_le hv hk) one_ne_zero ?_
  rw [circleChar_gaussStep_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussLam_nonneg hv)]

/-! ### Size of the gap -/

/-- `1 - cos θ(a) = 1 - √(1 - a²)` on acceptance and `0` on rejection. -/
theorem one_sub_cos_stepAngle (a : ℝ) :
    1 - cos (stepAngle a) = if |a| ≤ 1 then 1 - √(1 - a ^ 2) else 0 := by
  rw [cos_stepAngle]
  split_ifs <;> simp

theorem one_sub_sqrt_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 - √(1 - x) ≤ x := by
  have h : 1 - x ≤ √(1 - x) := by
    have h2 : 0 ≤ 1 - x := by linarith
    have h3 : 1 - x ≤ 1 := by linarith
    calc 1 - x = √(1 - x) * √(1 - x) := (Real.mul_self_sqrt h2).symm
      _ ≤ 1 * √(1 - x) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact Real.sqrt_le_one.mpr h3 |>.trans le_rfl
      _ = √(1 - x) := one_mul _
  linarith

theorem half_le_one_sub_sqrt {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 1) : x / 2 ≤ 1 - √(1 - x) := by
  have h2 : 0 ≤ 1 - x := by linarith
  have h : √(1 - x) ≤ 1 - x / 2 := by
    rw [show (1 - x / 2) = √((1 - x / 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg x]
  linarith

/-- Pointwise bounds on the one-step displacement. -/
theorem one_sub_cos_stepAngle_le (a : ℝ) : 1 - cos (stepAngle a) ≤ a ^ 2 := by
  rw [one_sub_cos_stepAngle]
  split_ifs with h
  · have h1 : a ^ 2 ≤ 1 := by
      have := abs_le.mp h
      nlinarith
    exact one_sub_sqrt_le (sq_nonneg a) h1
  · exact sq_nonneg a

theorem one_sub_cos_stepAngle_ge (a : ℝ) :
    (if |a| ≤ 1 then a ^ 2 / 2 else 0) ≤ 1 - cos (stepAngle a) := by
  rw [one_sub_cos_stepAngle]
  split_ifs with h
  · have h1 : a ^ 2 ≤ 1 := by
      have := abs_le.mp h
      nlinarith
    exact half_le_one_sub_sqrt (sq_nonneg a) h1
  · exact le_rfl

/-- The gap as an expectation: `1 - λ₁ = E[(1 - √(1 - a²)) 1_{|a| ≤ 1}]`. -/
theorem one_sub_gaussLam (v : ℝ≥0) :
    1 - gaussLam v
      = ∫ a, (if |a| ≤ 1 then 1 - √(1 - a ^ 2) else 0) ∂(gaussianReal 0 v) := by
  have hi := integrable_cos_mul_stepAngle (gaussianReal 0 v) 1
  simp only [one_mul] at hi
  have : ∫ a, (1 - cos (stepAngle a)) ∂(gaussianReal 0 v) = 1 - gaussLam v := by
    rw [integral_sub (integrable_const _) hi]
    simp [gaussLam]
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  exact one_sub_cos_stepAngle a

/-- Second moment of the centred Gaussian. -/
theorem integral_sq_gaussianReal (v : ℝ≥0) : ∫ a, a ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  have hmem : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 v) := memLp_id_gaussianReal 2
  rw [variance_eq_sub hmem] at h
  simp only [integral_id_gaussianReal] at h
  simpa using h

theorem integrable_sq_gaussianReal (v : ℝ≥0) : Integrable (fun a : ℝ => a ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

/-- **Upper bound on the gap:** `1 - λ₁ ≤ σ²`. -/
theorem one_sub_gaussLam_le (v : ℝ≥0) : 1 - gaussLam v ≤ v := by
  have hi := integrable_cos_mul_stepAngle (gaussianReal 0 v) 1
  simp only [one_mul] at hi
  have : ∫ a, (1 - cos (stepAngle a)) ∂(gaussianReal 0 v) = 1 - gaussLam v := by
    rw [integral_sub (integrable_const _) hi]
    simp [gaussLam]
  rw [← this, ← integral_sq_gaussianReal v]
  exact integral_mono ((integrable_const _).sub hi) (integrable_sq_gaussianReal v)
    one_sub_cos_stepAngle_le

/-- **Lower bound on the gap:** `1 - λ₁ ≥ ½ E[a²; |a| ≤ 1]`. -/
theorem one_sub_gaussLam_ge (v : ℝ≥0) :
    ∫ a, (if |a| ≤ 1 then a ^ 2 / 2 else 0) ∂(gaussianReal 0 v) ≤ 1 - gaussLam v := by
  have hi := integrable_cos_mul_stepAngle (gaussianReal 0 v) 1
  simp only [one_mul] at hi
  have : ∫ a, (1 - cos (stepAngle a)) ∂(gaussianReal 0 v) = 1 - gaussLam v := by
    rw [integral_sub (integrable_const _) hi]
    simp [gaussLam]
  rw [← this]
  refine integral_mono ?_ ((integrable_const _).sub hi) one_sub_cos_stepAngle_ge
  refine Integrable.mono' ((integrable_sq_gaussianReal v).div_const 2) ?_ ?_
  · exact (Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      (by fun_prop) measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a => ?_
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp
      positivity

end SOnMCMC

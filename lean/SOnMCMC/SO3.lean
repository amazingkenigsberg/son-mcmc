import SOnMCMC.CircleSampler

/-!
# `SO(3)`: the first character dominates on rotations of angle at most `π/2`

Paper: Section 6.

The irreducible representations of `SO(3)` have dimensions `2l + 1`, and the character of the
`l`-th one at a rotation of angle `θ` is `sin ((2l+1) θ/2) / sin (θ/2)` (classical; not
formalised here).  The eigenvalue of a conjugation-invariant walk on the `l`-th isotypic
component is the expectation of the *character ratio* `so3CharRatio l θ`.  We prove the analytic
statement that makes the first eigenvalue dominate:

* `abs_sin_mul_div_le`: `|sin (m x)| / m ≤ sin (3x) / 3` for `m ≥ 5` and `0 ≤ x ≤ π/4`;
* `abs_so3CharRatio_le`: `|χ_l(θ)| / (2l+1) ≤ χ_1(θ) / 3` for `l ≥ 1` and `0 ≤ θ ≤ π/2`;
* `so3_eigenvalue_dominated`: hence `|λ_l| ≤ λ_1` whenever the rotation angle of the step is
  almost surely in `[0, π/2]`, which is the case for the tangent-space sampler.
-/

open Real MeasureTheory Set

namespace SOnMCMC

/-- For `m ≥ 5` and `0 ≤ x ≤ π/4`: `|sin (m x)| / m ≤ sin (3 x) / 3`. -/
theorem abs_sin_mul_div_le {m : ℕ} (hm : 5 ≤ m) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ π / 4) :
    |sin (m * x)| / m ≤ sin (3 * x) / 3 := by
  have hm' : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hπ := pi_pos
  have h1 : |sin (m * x)| / m ≤ 1 / m :=
    div_le_div_of_nonneg_right (abs_sin_le_one _) hmpos.le
  by_cases hx6 : x ≤ π / 6
  · by_cases hmx : m * x ≤ π
    · -- concavity of `sin` on `[0, π]`
      have hconc := strictConcaveOn_sin_Icc.concaveOn
      have ha : (0 : ℝ) ≤ 3 / m := by positivity
      have hb : (0 : ℝ) ≤ 1 - 3 / m := by
        rw [sub_nonneg, div_le_one hmpos]
        linarith
      have h := hconc.2 (show (m : ℝ) * x ∈ Icc (0 : ℝ) π from ⟨by positivity, hmx⟩)
        (show (0 : ℝ) ∈ Icc (0 : ℝ) π from ⟨le_refl 0, hπ.le⟩) ha hb (by ring)
      simp only [smul_eq_mul, sin_zero, mul_zero, add_zero] at h
      have e : 3 / (m : ℝ) * (m * x) = 3 * x := by field_simp
      rw [e] at h
      have hs : 0 ≤ sin (m * x) := sin_nonneg_of_nonneg_of_le_pi (by positivity) hmx
      rw [abs_of_nonneg hs, div_le_div_iff₀ hmpos (by norm_num)]
      have h' : 3 * sin (m * x) ≤ sin (3 * x) * m := by
        have : 3 / (m : ℝ) * sin (m * x) = 3 * sin (m * x) / m := by ring
        rw [this, div_le_iff₀ hmpos] at h
        exact h
      linarith
    · -- Jordan's inequality
      push Not at hmx
      have hJ := mul_le_sin (x := 3 * x) (by positivity) (by linarith)
      have h2 : 1 / (m : ℝ) < x / π := by
        rw [div_lt_div_iff₀ hmpos hπ]
        linarith
      have h3 : x / π ≤ sin (3 * x) / 3 := by
        rw [div_le_div_iff₀ hπ (by norm_num)]
        have h4 : 2 / π * (3 * x) * π = 6 * x := by
          field_simp
          ring
        have h5 := mul_le_mul_of_nonneg_right hJ hπ.le
        rw [h4] at h5
        linarith
      linarith
  · -- `3x ∈ [π/2, 3π/4]`, where `sin ≥ √2/2`
    push Not at hx6
    have hs : sin (π / 4) ≤ sin (3 * x) := by
      rw [← sin_pi_sub (3 * x)]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    rw [sin_pi_div_four] at hs
    have h2 : 1 / (m : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hm'
    have h3 : (1.4 : ℝ) ≤ √2 := by
      rw [show (1.4 : ℝ) = √(1.4 ^ 2) from (sqrt_sq (by norm_num)).symm]
      exact sqrt_le_sqrt (by norm_num)
    linarith

/-- The normalised character `χ_l(θ) / (2l+1)` of the `(2l+1)`-dimensional irreducible
representation of `SO(3)` at a rotation of angle `θ`, with value `1` at the identity. -/
noncomputable def so3CharRatio (l : ℕ) (θ : ℝ) : ℝ :=
  if sin (θ / 2) = 0 then 1
  else sin ((2 * l + 1 : ℕ) * (θ / 2)) / ((2 * l + 1 : ℕ) * sin (θ / 2))

/-- For `l = 1` (the standard representation) the ratio is `(1 + 2 cos θ) / 3 = tr R / 3`. -/
theorem so3CharRatio_one_eq (θ : ℝ) : so3CharRatio 1 θ = (1 + 2 * cos θ) / 3 := by
  have hcos : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    have h1 := cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h1
    have h2 := sin_sq_add_cos_sq (θ / 2)
    nlinarith
  unfold so3CharRatio
  split_ifs with h
  · rw [hcos, h]
    norm_num
  · have h3 : ((2 * 1 + 1 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3, sin_three_mul, hcos]
    field_simp
    ring

/-- Character ratios are bounded by `1`. -/
theorem abs_so3CharRatio_le_one (l : ℕ) (θ : ℝ) : |so3CharRatio l θ| ≤ 1 := by
  unfold so3CharRatio
  split_ifs with h
  · simp
  · have hm : (0 : ℝ) < ((2 * l + 1 : ℕ) : ℝ) := by positivity
    rw [abs_div, abs_mul, abs_of_pos hm,
      div_le_one (mul_pos hm (abs_pos.mpr h))]
    exact abs_sin_nat_mul_le (2 * l + 1) (θ / 2)

/-- **Theorem (domination by the first character).** For `l ≥ 1` and a rotation angle
`0 ≤ θ ≤ π/2`: `|χ_l(θ)| / (2l+1) ≤ χ_1(θ) / 3`. -/
theorem abs_so3CharRatio_le {l : ℕ} (hl : 1 ≤ l) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    |so3CharRatio l θ| ≤ so3CharRatio 1 θ := by
  by_cases hs : sin (θ / 2) = 0
  · simp [so3CharRatio, hs]
  · have hx0 : 0 ≤ θ / 2 := by linarith
    have hx1 : θ / 2 ≤ π / 4 := by linarith
    have hspos : 0 < sin (θ / 2) :=
      lt_of_le_of_ne (sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [pi_pos])) (Ne.symm hs)
    rcases Nat.lt_or_ge l 2 with hl2 | hl2
    · have hl1 : l = 1 := by omega
      subst hl1
      rw [abs_of_nonneg]
      rw [so3CharRatio_one_eq]
      have := cos_nonneg_of_mem_Icc (x := θ) ⟨by linarith [pi_pos], h1⟩
      positivity
    · have hm : 5 ≤ 2 * l + 1 := by omega
      have key := abs_sin_mul_div_le hm hx0 hx1
      have hmpos : (0 : ℝ) < ((2 * l + 1 : ℕ) : ℝ) := by positivity
      have h3 : ((2 * 1 + 1 : ℕ) : ℝ) = 3 := by norm_num
      simp only [so3CharRatio, hs, ↓reduceIte]
      rw [h3, abs_div, abs_mul, abs_of_pos hspos, abs_of_pos hmpos, ← div_div, ← div_div]
      exact div_le_div_of_nonneg_right key hspos.le

theorem measurable_so3CharRatio (l : ℕ) : Measurable (so3CharRatio l) := by
  unfold so3CharRatio
  refine Measurable.ite ?_ measurable_const (by fun_prop)
  exact (isClosed_eq (by fun_prop) continuous_const).measurableSet

/-- **Corollary (the first eigenvalue dominates on `SO(3)`).** If the rotation angle `θ` of the
step is almost surely in `[0, π/2]`, then `|E[χ_l(θ)] / (2l+1)| ≤ E[χ_1(θ)] / 3` for all
`l ≥ 1`. -/
theorem so3_eigenvalue_dominated (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) (π / 2)) {l : ℕ} (hl : 1 ≤ l) :
    |∫ θ, so3CharRatio l θ ∂μ| ≤ ∫ θ, so3CharRatio 1 θ ∂μ := by
  have hint : ∀ l, Integrable (so3CharRatio l) μ := fun l =>
    Integrable.of_bound (measurable_so3CharRatio l).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (abs_so3CharRatio_le_one l))
  calc |∫ θ, so3CharRatio l θ ∂μ| ≤ ∫ θ, |so3CharRatio l θ| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ θ, so3CharRatio 1 θ ∂μ :=
        integral_mono_ae (hint l).abs (hint 1)
          (hμ.mono fun θ hθ => abs_so3CharRatio_le hl hθ.1 hθ.2)

end SOnMCMC

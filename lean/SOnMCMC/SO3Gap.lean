import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import SOnMCMC.GaussianSampler
import SOnMCMC.SO3Cover

/-!
# The spectral gap of conjugation-invariant walks on `SO(3)`

Paper: Section 6.6.

For a conjugation-invariant step distribution `ν` on `SO(3)` whose steps almost surely have a
positive semidefinite symmetric part (rotation angle at most `π/2`), which is the case for the
tangent-space sampler:

* `so3_l2ContractionBound`: `‖P f‖₂ ≤ λ ‖f‖₂` for mean-zero `f ∈ L²`, with `λ = E[tr R]/3`;
* `so3_isSpectralGap`: the spectral gap is exactly `1 - λ`;
* `so3_isLeast_contraction`: the `L²` contraction coefficient is exactly `λ`;
* `gaussSO_three_isSpectralGap`: the instance for the Gaussian tangent-space sampler.

The proof decomposes `ν` into conjugacy classes (`integral_norm_sq_markovOp_le_of_class`), lifts
each class to `SU(2)` along the double cover (`so3_class_l2Bound`), and uses the bound
`su2_class_l2Bound` proved there.
-/

open MeasureTheory Matrix Real
open scoped ComplexConjugate NNReal

namespace SOnMCMC

/-! ### A weighted Cauchy–Schwarz inequality -/

/-- **Weighted Cauchy–Schwarz.** `|∫ h|² ≤ (∫ w) (∫ |h|²/w)` for a positive weight `w`. -/
theorem norm_integral_sq_le_weighted {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {h : α → ℂ} {w : α → ℝ} (hw : ∀ a, 0 < w a) (hwi : Integrable w ν) (hh : Integrable h ν)
    (hhw : Integrable (fun a => ‖h a‖ ^ 2 / w a) ν) :
    ‖∫ a, h a ∂ν‖ ^ 2 ≤ (∫ a, w a ∂ν) * ∫ a, ‖h a‖ ^ 2 / w a ∂ν := by
  have hquad : ∀ s : ℝ, 0 ≤ (∫ a, w a ∂ν) * (s * s) + (-2 * ∫ a, ‖h a‖ ∂ν) * s
      + ∫ a, ‖h a‖ ^ 2 / w a ∂ν := by
    intro s
    have hpt : ∀ a, 0 ≤ s * s * w a - 2 * s * ‖h a‖ + ‖h a‖ ^ 2 / w a := by
      intro a
      have e : s * s * w a - 2 * s * ‖h a‖ + ‖h a‖ ^ 2 / w a = (s * w a - ‖h a‖) ^ 2 / w a := by
        have := (hw a).ne'
        field_simp
        ring
      rw [e]
      exact div_nonneg (sq_nonneg _) (hw a).le
    have hint : 0 ≤ ∫ a, (s * s * w a - 2 * s * ‖h a‖ + ‖h a‖ ^ 2 / w a) ∂ν :=
      integral_nonneg hpt
    have e : ∫ a, (s * s * w a - 2 * s * ‖h a‖ + ‖h a‖ ^ 2 / w a) ∂ν
        = (∫ a, w a ∂ν) * (s * s) + (-2 * ∫ a, ‖h a‖ ∂ν) * s + ∫ a, ‖h a‖ ^ 2 / w a ∂ν := by
      have i1 : Integrable (fun a => s * s * w a) ν := hwi.const_mul _
      have i2 : Integrable (fun a => 2 * s * ‖h a‖) ν := hh.norm.const_mul _
      have i12 : Integrable (fun a => s * s * w a - 2 * s * ‖h a‖) ν := i1.sub i2
      rw [integral_add i12 hhw, integral_sub i1 i2, integral_const_mul, integral_const_mul]
      ring
    rw [e] at hint
    exact hint
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  have hI : ‖∫ a, h a ∂ν‖ ≤ ∫ a, ‖h a‖ ∂ν := norm_integral_le_integral_norm h
  have hI2 := pow_le_pow_left₀ (norm_nonneg _) hI 2
  nlinarith

/-! ### Decomposition of a conjugation-invariant walk into conjugacy classes -/

section ClassDecomposition

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **From conjugacy classes to conjugation-invariant measures.** If the walk on each conjugacy
class contracts `f` by the factor `w R`, then the walk with a conjugation-invariant step
distribution `ν` contracts `f` by the factor `∫ w dν`. -/
theorem integral_norm_sq_markovOp_le_of_class (m ν : Measure G) [IsProbabilityMeasure m]
    [m.IsMulRightInvariant] [IsProbabilityMeasure ν] (hν : IsConjInvariant ν)
    {f : G → ℂ} (hf : Continuous f) {w : G → ℝ} (hwc : Continuous w) (hwpos : ∀ R, 0 < w R)
    (hclass : ∀ᵐ R ∂ν, ∫ x, ‖markovOp (classMeasure m R) f x‖ ^ 2 ∂m
      ≤ w R ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂m) :
    ∫ x, ‖markovOp ν f x‖ ^ 2 ∂m ≤ (∫ R, w R ∂ν) ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂m := by
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  -- the class operator as a function of `(x, R)`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G × G → ℂ, ∀ p, Φ p = ∫ g, f (p.1 * (g * p.2 * g⁻¹)) ∂m :=
    ⟨_, fun _ => rfl⟩
  have hΦc : Continuous Φ := by
    have e : Φ = fun p : G × G => ∫ g, f (p.1 * (g * p.2 * g⁻¹)) ∂m := funext hΦ
    rw [e]
    refine continuous_of_dominated (bound := fun _ => C) (fun p => ?_) (fun p => ?_)
      (integrable_const C) ?_
    · exact (hf.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun g => hC _ ⟨_, rfl⟩
    · exact Filter.Eventually.of_forall fun g => hf.comp (by fun_prop)
  have hΦeq : ∀ x R, markovOp (classMeasure m R) f x = Φ (x, R) := by
    intro x R
    rw [hΦ]
    exact integral_classMeasure m R (F := fun r => f (x * r))
      (hf.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  -- the walk is the average of the class walks
  have hdecomp : ∀ x, markovOp ν f x = ∫ R, Φ (x, R) ∂ν := by
    intro x
    have hint : Integrable (fun p : G × G => f (x * (p.2 * p.1 * p.2⁻¹))) (ν.prod m) :=
      (hf.comp (by fun_prop)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hswap := integral_integral_swap (f := fun (R g : G) => f (x * (g * R * g⁻¹))) hint
    have hinner : ∀ g : G, ∫ R, f (x * (g * R * g⁻¹)) ∂ν = markovOp ν f x := by
      intro g
      have h := integral_map (μ := ν) (measurable_conj_right g).aemeasurable
        (f := fun r => f (x * r))
        (hf.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      rw [hν g] at h
      exact h.symm
    simp only [hΦ]
    rw [hswap]
    simp only [hinner]
    simp
  have hA0 : 0 ≤ ∫ R, w R ∂ν := integral_nonneg fun R => (hwpos R).le
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : G × G → ℝ, ∀ p, Ψ p = ‖Φ p‖ ^ 2 / w p.2 := ⟨_, fun _ => rfl⟩
  have hΨc : Continuous Ψ := by
    have e : Ψ = fun p : G × G => ‖Φ p‖ ^ 2 / w p.2 := funext hΨ
    rw [e]
    exact (hΦc.norm.pow 2).div (hwc.comp continuous_snd) fun p => (hwpos p.2).ne'
  have hΨint : Integrable Ψ (m.prod ν) :=
    hΨc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwint : Integrable w ν :=
    hwc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- weighted Cauchy–Schwarz, pointwise in `x`
  have hpt : ∀ x, ‖markovOp ν f x‖ ^ 2 ≤ (∫ R, w R ∂ν) * ∫ R, Ψ (x, R) ∂ν := by
    intro x
    have hx : Continuous fun R : G => (x, R) := continuous_const.prodMk continuous_id
    have h1 := norm_integral_sq_le_weighted ν (h := fun R => Φ (x, R)) hwpos hwint
      ((hΦc.comp hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((((hΦc.comp hx).norm.pow 2).div hwc fun R => (hwpos R).ne').integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    rw [hdecomp x]
    simpa only [hΨ] using h1
  have hmem := memLp_markovOp m ν (memLp_of_continuous_compact m hf)
  have hPint : Integrable (fun x => ‖markovOp ν f x‖ ^ 2) m :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hΨx : Integrable (fun x => ∫ R, Ψ (x, R) ∂ν) m := hΨint.integral_prod_left
  have h1 : ∫ x, ‖markovOp ν f x‖ ^ 2 ∂m ≤ (∫ R, w R ∂ν) * ∫ x, ∫ R, Ψ (x, R) ∂ν ∂m := by
    rw [← integral_const_mul]
    exact integral_mono hPint (hΨx.const_mul _) hpt
  have hswap : ∫ x, ∫ R, Ψ (x, R) ∂ν ∂m = ∫ R, ∫ x, Ψ (x, R) ∂m ∂ν :=
    integral_integral_swap (f := fun x R => Ψ (x, R)) hΨint
  have h2 : ∫ R, ∫ x, Ψ (x, R) ∂m ∂ν ≤ ∫ R, w R * ∫ x, ‖f x‖ ^ 2 ∂m ∂ν := by
    refine integral_mono_ae hΨint.integral_prod_right (hwint.mul_const _) ?_
    filter_upwards [hclass] with R hR
    simp only [hΨ, hΦeq] at hR ⊢
    rw [integral_div, div_le_iff₀ (hwpos R)]
    calc ∫ x, ‖Φ (x, R)‖ ^ 2 ∂m ≤ w R ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂m := hR
      _ = w R * (∫ x, ‖f x‖ ^ 2 ∂m) * w R := by ring
  calc ∫ x, ‖markovOp ν f x‖ ^ 2 ∂m ≤ (∫ R, w R ∂ν) * ∫ x, ∫ R, Ψ (x, R) ∂ν ∂m := h1
    _ = (∫ R, w R ∂ν) * ∫ R, ∫ x, Ψ (x, R) ∂m ∂ν := by rw [hswap]
    _ ≤ (∫ R, w R ∂ν) * ∫ R, w R * ∫ x, ‖f x‖ ^ 2 ∂m ∂ν := mul_le_mul_of_nonneg_left h2 hA0
    _ = (∫ R, w R ∂ν) ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂m := by
        rw [integral_mul_const]
        ring

end ClassDecomposition

/-! ### Transfer along the covering map -/

/-- **The covering map sends Haar measure to Haar measure.** -/
theorem measurePreserving_cover : MeasurePreserving (cover : SU2 → SO 3) haarSU2 (haarSO 3) :=
  cover.measurePreserving continuous_cover cover_surjective (by rw [measure_univ, measure_univ])

theorem integral_comp_cover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : SO 3 → E}
    (hh : AEStronglyMeasurable h (haarSO 3)) :
    ∫ x, h (cover x) ∂haarSU2 = ∫ y, h y ∂haarSO 3 := by
  have hmp := measurePreserving_cover
  have hh' : AEStronglyMeasurable h (Measure.map cover haarSU2) := by
    rw [hmp.map_eq]
    exact hh
  rw [← integral_map hmp.measurable.aemeasurable hh', hmp.map_eq]

theorem markovOp_cover (ν' : Measure SU2) {f : SO 3 → ℂ} (hf : Continuous f) (x : SU2) :
    markovOp (ν'.map cover) f (cover x) = markovOp ν' (f ∘ cover) x := by
  simp only [markovOp, Function.comp]
  have hc : Continuous fun g : SO 3 => f (cover x * g) :=
    hf.comp (continuous_const.mul continuous_id)
  rw [integral_map continuous_cover.measurable.aemeasurable hc.aestronglyMeasurable]
  simp only [map_mul]

/-- The class measure of `cover q₀` is the image of the class measure of `q₀`. -/
theorem classMeasure_cover (q₀ : SU2) :
    (classMeasure haarSU2 q₀).map cover = classMeasure (haarSO 3) (cover q₀) := by
  have hc := continuous_cover.measurable
  have hcomp : (cover : SU2 → SO 3) ∘ (fun g : SU2 => g * q₀ * g⁻¹)
      = (fun R : SO 3 => R * cover q₀ * R⁻¹) ∘ cover := by
    funext g
    simp
  rw [classMeasure, classMeasure, Measure.map_map hc (measurable_conj_left q₀), hcomp,
    ← Measure.map_map (measurable_conj_left (cover q₀)) hc, measurePreserving_cover.map_eq]

theorem one_le_trace_of_posSemidef (R : SO 3)
    (hP : (symPart (R : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    1 ≤ (R : Matrix (Fin 3) (Fin 3) ℝ).trace := by
  obtain ⟨q, rfl⟩ := cover_surjective R
  have h := one_le_of_posSemidef_symPart q hP
  rw [coe_cover, trace_covMat]
  linarith

/-- **The `L²` bound for a conjugacy class of `SO(3)`.** If the symmetric part of `R₀` is
positive semidefinite, the walk whose steps are uniform on the conjugacy class of `R₀` contracts
continuous mean-zero functions by the factor `tr R₀ / 3`. -/
theorem so3_class_l2Bound (R₀ : SO 3)
    (hP : (symPart (R₀ : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) {f : SO 3 → ℂ}
    (hf : Continuous f) (hmean : ∫ x, f x ∂haarSO 3 = 0) :
    ∫ x, ‖markovOp (classMeasure (haarSO 3) R₀) f x‖ ^ 2 ∂haarSO 3
      ≤ ((R₀ : Matrix (Fin 3) (Fin 3) ℝ).trace / 3) ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂haarSO 3 := by
  obtain ⟨q₁, hq₁⟩ := cover_surjective R₀
  -- choose the lift with nonnegative real part
  obtain ⟨q₀, hq₀, hre⟩ : ∃ q₀ : SU2, cover q₀ = R₀ ∧ 0 ≤ (q₀.1 0 0).re := by
    by_cases h : 0 ≤ (q₁.1 0 0).re
    · exact ⟨q₁, hq₁, h⟩
    · refine ⟨negOne * q₁, by rw [cover_negOne_mul, hq₁], ?_⟩
      have e : (negOne * q₁ : SU2).1 0 0 = -q₁.1 0 0 := by
        rw [SU2.coe_mul, negOne, SU2.mk'_coe]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [e, Complex.neg_re]
      push Not at h
      linarith
  subst hq₀
  have hc1 : 1 ≤ 2 * (q₀.1 0 0).re ^ 2 := one_le_of_posSemidef_symPart q₀ hP
  have htr : ((cover q₀ : SO 3) : Matrix (Fin 3) (Fin 3) ℝ).trace / 3
      = (4 * (q₀.1 0 0).re ^ 2 - 1) / 3 := by
    rw [coe_cover, trace_covMat]
  rw [htr, ← classMeasure_cover]
  have hFc : Continuous (f ∘ cover) := hf.comp continuous_cover
  have heven : ∀ x, (f ∘ cover) (negOne * x) = (f ∘ cover) x := fun x => by
    simp only [Function.comp, cover_negOne_mul]
  have hmeanF : ∫ x, (f ∘ cover) x ∂haarSU2 = 0 := by
    rw [← hmean]
    exact integral_comp_cover hf.aestronglyMeasurable
  have key := su2_class_l2Bound q₀ hre hc1 hFc heven hmeanF
  have hfL : MemLp f 2 (haarSO 3) := memLp_of_continuous_compact _ hf
  have : IsProbabilityMeasure ((classMeasure haarSU2 q₀).map cover) :=
    Measure.isProbabilityMeasure_map continuous_cover.measurable.aemeasurable
  have hPL := memLp_markovOp (haarSO 3) ((classMeasure haarSU2 q₀).map cover) hfL
  have h1 : ∫ x, ‖markovOp (classMeasure haarSU2 q₀) (f ∘ cover) x‖ ^ 2 ∂haarSU2
      = ∫ y, ‖markovOp ((classMeasure haarSU2 q₀).map cover) f y‖ ^ 2 ∂haarSO 3 := by
    rw [← integral_comp_cover
      ((memLp_two_iff_integrable_sq_norm hPL.aestronglyMeasurable).mp hPL).aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖markovOp (classMeasure haarSU2 q₀) (f ∘ cover) x‖ ^ 2
      = ‖markovOp ((classMeasure haarSU2 q₀).map cover) f (cover x)‖ ^ 2
    rw [markovOp_cover _ hf x]
  have h2 : ∫ x, ‖(f ∘ cover) x‖ ^ 2 ∂haarSU2 = ∫ y, ‖f y‖ ^ 2 ∂haarSO 3 :=
    integral_comp_cover (hf.norm.pow 2).aestronglyMeasurable
  rw [h1, h2] at key
  exact key

/-! ### The spectral gap on `SO(3)` -/

/-- Conjugation invariance under `O(n)` implies conjugation invariance under `SO(n)`. -/
theorem ConjInvariant.isConjInvariant {n : ℕ} {ν : Measure (SO n)} (hν : ConjInvariant ν) :
    IsConjInvariant ν := by
  intro g
  have h := hν ⟨g.1, SO.coe_mem_orthogonal g⟩
  have e : (fun R : SO n => g * R * g⁻¹) = conjO ⟨g.1, SO.coe_mem_orthogonal g⟩ := by
    funext R
    apply Subtype.ext
    show g.1 * R.1 * star g.1 = g.1 * R.1 * (g.1)ᵀ
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [e]
  exact h

/-- The bound for continuous functions. -/
theorem so3_l2Bound_continuous (ν : Measure (SO 3)) [IsProbabilityMeasure ν]
    (hν : IsConjInvariant ν)
    (hpsd : ∀ᵐ R : SO 3 ∂ν, (symPart (R : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef)
    {f : SO 3 → ℂ} (hf : Continuous f) (hmean : ∫ x, f x ∂haarSO 3 = 0) :
    ∫ x, ‖markovOp ν f x‖ ^ 2 ∂haarSO 3 ≤ stdEig ν ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂haarSO 3 := by
  have htrc : Continuous fun R : SO 3 => (R : Matrix (Fin 3) (Fin 3) ℝ).trace :=
    continuous_subtype_val.matrix_trace
  obtain ⟨w, hw⟩ : ∃ w : SO 3 → ℝ,
      ∀ R, w R = max ((R : Matrix (Fin 3) (Fin 3) ℝ).trace / 3) (1 / 3) := ⟨_, fun _ => rfl⟩
  have hwc : Continuous w := by
    have e : w = fun R : SO 3 => max ((R : Matrix (Fin 3) (Fin 3) ℝ).trace / 3) (1 / 3) :=
      funext hw
    rw [e]
    exact (htrc.div_const 3).max continuous_const
  have hwpos : ∀ R, 0 < w R := fun R => by
    rw [hw]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hweq : ∀ᵐ R : SO 3 ∂ν, w R = (R : Matrix (Fin 3) (Fin 3) ℝ).trace / 3 := by
    filter_upwards [hpsd] with R hR
    have := one_le_trace_of_posSemidef R hR
    rw [hw]
    exact max_eq_left (by linarith)
  have hclass : ∀ᵐ R ∂ν, ∫ x, ‖markovOp (classMeasure (haarSO 3) R) f x‖ ^ 2 ∂haarSO 3
      ≤ w R ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂haarSO 3 := by
    filter_upwards [hpsd, hweq] with R hR hwR
    rw [hwR]
    exact so3_class_l2Bound R hR hf hmean
  have key := integral_norm_sq_markovOp_le_of_class (haarSO 3) ν hν hf hwc hwpos hclass
  have hint : ∫ R, w R ∂ν = stdEig ν := by
    rw [integral_congr_ae hweq, integral_div, stdEig]
    norm_num
  rwa [hint] at key

instance SO.instPseudoMetrizableSpace {n : ℕ} : TopologicalSpace.PseudoMetrizableSpace (SO n) :=
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin n → Fin n → ℝ))
  inferInstance

/-- **`L²` contraction on `SO(3)`** for the group-conjugation-invariant version. -/
theorem so3_l2ContractionBound_of_isConjInvariant (ν : Measure (SO 3)) [IsProbabilityMeasure ν]
    (hν : IsConjInvariant ν)
    (hpsd : ∀ᵐ R : SO 3 ∂ν, (symPart (R : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    L2ContractionBound (haarSO 3) ν (stdEig ν) := by
  intro f hf hmean
  refine integral_norm_sq_markovOp_le_of_approx (haarSO 3) ν hf fun ε hε => ?_
  have hf' : MemLp f (ENNReal.ofReal 2) (haarSO 3) := by
    rwa [show ENNReal.ofReal 2 = 2 by norm_num]
  obtain ⟨g, hg, -⟩ := hf'.exists_boundedContinuous_integral_rpow_sub_le
    (by norm_num : (0 : ℝ) < 2) (ε := ε / 4) (by positivity)
  simp only [Real.rpow_two] at hg
  have hgc : Continuous (g : SO 3 → ℂ) := g.continuous
  have hgL : MemLp (g : SO 3 → ℂ) 2 (haarSO 3) := memLp_of_continuous_compact _ hgc
  have hfg : MemLp (fun x => f x - g x) 2 (haarSO 3) := hf.sub hgL
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ∫ x, g x ∂haarSO 3 := ⟨_, rfl⟩
  have hc_le : ‖c‖ ^ 2 ≤ ∫ x, ‖f x - g x‖ ^ 2 ∂haarSO 3 := by
    have h1 : c = -∫ x, (f x - g x) ∂haarSO 3 := by
      rw [integral_sub (hf.integrable one_le_two) (hgL.integrable one_le_two), hmean, zero_sub,
        neg_neg, hc]
    rw [h1, norm_neg]
    exact norm_integral_sq_le (haarSO 3) hfg
  refine ⟨fun x => g x - c, memLp_of_continuous_compact _ (hgc.sub continuous_const), ?_, ?_⟩
  · have e : ∀ x, f x - (g x - c) = (f x - g x) + c := fun x => by ring
    simp only [e]
    have h2 := integral_sq_norm_add_le (haarSO 3) hfg (memLp_const c) (δ := 1) one_pos
    simp only [integral_const, probReal_univ, one_smul] at h2
    norm_num at h2
    linarith
  · refine so3_l2Bound_continuous ν hν hpsd (hgc.sub continuous_const) ?_
    rw [integral_sub (hgL.integrable one_le_two) (integrable_const c), integral_const, ← hc]
    simp

variable {ν : Measure (SO 3)} [IsProbabilityMeasure ν]

/-- **Theorem (`L²` contraction on `SO(3)`).** For a conjugation-invariant step distribution on
`SO(3)` whose steps almost surely have positive semidefinite symmetric part,
`‖P f‖₂ ≤ λ ‖f‖₂` for every mean-zero `f ∈ L²`, where `λ = E[tr R]/3`. -/
theorem so3_l2ContractionBound (hν : ConjInvariant ν)
    (hpsd : ∀ᵐ R : SO 3 ∂ν, (symPart (R : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    L2ContractionBound (haarSO 3) ν (stdEig ν) :=
  so3_l2ContractionBound_of_isConjInvariant ν hν.isConjInvariant hpsd

/-- `λ = E[tr R]/3 ≥ 1/3` when the steps have positive semidefinite symmetric part. -/
theorem one_third_le_stdEig
    (hpsd : ∀ᵐ R : SO 3 ∂ν, (symPart (R : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    1 / 3 ≤ stdEig ν := by
  have h : (1 : ℝ) ≤ ∫ R : SO 3, (R : Matrix (Fin 3) (Fin 3) ℝ).trace ∂ν := by
    have h1 := integral_mono_ae (μ := ν) (integrable_const (1 : ℝ)) (integrable_trace ν)
      (hpsd.mono fun R hR => one_le_trace_of_posSemidef R hR)
    simpa using h1
  rw [stdEig]
  norm_num
  linarith

/-- **Theorem (Poincaré inequality on `SO(3)`).** -/
theorem so3_poincareIneq (hν : ConjInvariant ν)
    (hpsd : ∀ᵐ R : SO 3 ∂ν, (symPart (R : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    PoincareIneq (haarSO 3) ν (1 - stdEig ν) :=
  (so3_l2ContractionBound hν hpsd).poincareIneq
    (le_trans (by norm_num) (one_third_le_stdEig hpsd))

/-- **Theorem (the spectral gap on `SO(3)`).** For a conjugation-invariant step distribution on
`SO(3)` whose steps almost surely have positive semidefinite symmetric part, the spectral gap of
the walk is exactly `1 - E[tr R]/3`. -/
theorem so3_isSpectralGap (hν : ConjInvariant ν)
    (hpsd : ∀ᵐ R : SO 3 ∂ν, (symPart (R : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    IsSpectralGap (haarSO 3) ν (1 - stdEig ν) :=
  ⟨so3_poincareIneq hν hpsd, fun _ hγ => gap_le_of_conjInvariant (by norm_num) ν hν hγ⟩

/-- **Theorem (the `L²` contraction coefficient on `SO(3)`).** It is exactly `E[tr R]/3`. -/
theorem so3_isLeast_contraction (hν : ConjInvariant ν)
    (hpsd : ∀ᵐ R : SO 3 ∂ν, (symPart (R : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef) :
    IsLeast {ρ : ℝ | 0 ≤ ρ ∧ L2ContractionBound (haarSO 3) ν ρ} (stdEig ν) := by
  refine ⟨⟨le_trans (by norm_num) (one_third_le_stdEig hpsd), so3_l2ContractionBound hν hpsd⟩,
    fun ρ hρ => ?_⟩
  have h := gap_le_of_conjInvariant (by norm_num) ν hν (hρ.2.poincareIneq hρ.1)
  linarith

/-! ### The Gaussian tangent-space sampler on `SO(3)` -/

/-- Every step of the sampler has positive semidefinite symmetric part. -/
theorem ae_posSemidef_gaussSOStep (n : ℕ) (v : ℝ≥0) :
    ∀ᵐ R : SO n ∂(gaussSOStep n v), (symPart (R : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  have hcont : Continuous fun R : SO n => symPart (R : Matrix (Fin n) (Fin n) ℝ) := by
    have h1 : Continuous fun R : SO n => (R : Matrix (Fin n) (Fin n) ℝ) :=
      continuous_subtype_val
    have h2 : Continuous fun R : SO n =>
        (R : Matrix (Fin n) (Fin n) ℝ) + (R : Matrix (Fin n) (Fin n) ℝ)ᵀ :=
      h1.add h1.matrix_transpose
    exact h2.const_smul (1 / 2 : ℝ)
  have hclosed : IsClosed {R : SO n | (symPart (R : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage hcont
  rw [gaussSOStep, ae_map_iff (measurable_gaussStepFun v).aemeasurable hclosed.measurableSet]
  exact Filter.Eventually.of_forall fun x => posSemidef_symPart_principalStep _

/-- **Theorem (the Gaussian sampler on `SO(3)`).** The spectral gap of the tangent-space sampler
on `SO(3)` with Gaussian proposals of variance `v` is exactly `1 - E[tr R]/3`. -/
theorem gaussSO_three_isSpectralGap (v : ℝ≥0) :
    IsSpectralGap (haarSO 3) (gaussSOStep 3 v) (1 - stdEig (gaussSOStep 3 v)) :=
  so3_isSpectralGap (gaussSOStep_conjInvariant 3 v) (ae_posSemidef_gaussSOStep 3 v)

/-- The `L²` contraction coefficient of the Gaussian sampler on `SO(3)` is `E[tr R]/3`. -/
theorem gaussSO_three_isLeast_contraction (v : ℝ≥0) :
    IsLeast {ρ : ℝ | 0 ≤ ρ ∧ L2ContractionBound (haarSO 3) (gaussSOStep 3 v) ρ}
      (stdEig (gaussSOStep 3 v)) :=
  so3_isLeast_contraction (gaussSOStep_conjInvariant 3 v) (ae_posSemidef_gaussSOStep 3 v)

end SOnMCMC

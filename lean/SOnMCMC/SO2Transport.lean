import SOnMCMC.GapAsymptotics
import SOnMCMC.SO2
import SOnMCMC.SOn

/-!
# Transport of the circle results to the matrix group `SO(2)`

Paper: Section 4.5.

The theorems of `SOnMCMC.CircleSampler` are stated for the walk on `ℝ / 2πℤ`.  Here they are
transported to the matrix group along `θ ↦ R_θ`:

* `circleHomeo`: `θ ↦ R_θ` induces a homeomorphism `ℝ / 2πℤ ≃ₜ SO(2)` which is a group
  isomorphism (`circleToSO_add`) and maps Haar measure to Haar measure (`map_circleToSO_haar`);
* `poincareIneq_map_iff`, `l2ContractionBound_map_iff`, `isSpectralGap_map_iff`: Poincaré
  inequalities, contraction bounds and spectral gaps are invariant under a measurable isomorphism
  from an additive to a multiplicative group;
* `so2_isSpectralGap`, `so2_isLeast_contraction`: the walk on `SO(2)` whose step is the rotation
  matrix `R_{θ(a)}`, `a ∼ N(0, v)`, has spectral gap `1 - λ₁` and `L²` contraction coefficient
  `λ₁`.
-/

open MeasureTheory Real
open scoped NNReal

namespace SOnMCMC

/-! ### Transport along a measurable group isomorphism -/

section Transport

variable {A G : Type*} [AddGroup A] [Group G] [MeasurableSpace A] [MeasurableSpace G]

/-- The Markov operators correspond under a measurable group isomorphism. -/
theorem markovOp_map_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : A ≃ᵐ G)
    (hφ : ∀ x y, φ (x + y) = φ x * φ y) (ν : Measure A) (F : G → E) (x : A) :
    markovOp (ν.map φ) F (φ x) = addMarkovOp ν (F ∘ φ) x := by
  simp only [markovOp, addMarkovOp, Function.comp]
  rw [φ.measurableEmbedding.integral_map]
  simp only [hφ]

/-- Poincaré inequalities are transported by a measurable group isomorphism. -/
theorem poincareIneq_map_iff (φ : A ≃ᵐ G) (hφ : ∀ x y, φ (x + y) = φ x * φ y) (m ν : Measure A)
    (γ : ℝ) : PoincareIneq (m.map φ) (ν.map φ) γ ↔ AddPoincareIneq m ν γ := by
  have key : ∀ F : G → ℝ,
      (MemLp F 2 (m.map φ) ↔ MemLp (F ∘ φ) 2 m) ∧
      ∫ X, F X ∂(m.map φ) = ∫ x, (F ∘ φ) x ∂m ∧
      ∫ X, F X * markovOp (ν.map φ) F X ∂(m.map φ)
        = ∫ x, (F ∘ φ) x * addMarkovOp ν (F ∘ φ) x ∂m ∧
      ∫ X, F X ^ 2 ∂(m.map φ) = ∫ x, (F ∘ φ) x ^ 2 ∂m := by
    intro F
    refine ⟨φ.measurableEmbedding.memLp_map_measure_iff, ?_, ?_, ?_⟩
    · rw [φ.measurableEmbedding.integral_map]
      rfl
    · rw [φ.measurableEmbedding.integral_map]
      simp only [markovOp_map_apply φ hφ, Function.comp]
    · rw [φ.measurableEmbedding.integral_map]
      rfl
  constructor
  · intro h f hf hmean
    have hF : (f ∘ φ.symm) ∘ φ = f := by
      funext x
      simp
    obtain ⟨k1, k2, k3, k4⟩ := key (f ∘ φ.symm)
    rw [hF] at k1 k2 k3 k4
    have := h (f ∘ φ.symm) (k1.mpr hf) (k2.trans hmean)
    rwa [k3, k4] at this
  · intro h F hF hmean
    obtain ⟨k1, k2, k3, k4⟩ := key F
    rw [k3, k4]
    exact h (F ∘ φ) (k1.mp hF) (k2.symm.trans hmean)

/-- `L²` contraction bounds are transported by a measurable group isomorphism. -/
theorem l2ContractionBound_map_iff (φ : A ≃ᵐ G) (hφ : ∀ x y, φ (x + y) = φ x * φ y)
    (m ν : Measure A) (ρ : ℝ) :
    L2ContractionBound (m.map φ) (ν.map φ) ρ ↔ AddL2ContractionBound m ν ρ := by
  have key : ∀ F : G → ℂ,
      (MemLp F 2 (m.map φ) ↔ MemLp (F ∘ φ) 2 m) ∧
      ∫ X, F X ∂(m.map φ) = ∫ x, (F ∘ φ) x ∂m ∧
      ∫ X, ‖markovOp (ν.map φ) F X‖ ^ 2 ∂(m.map φ)
        = ∫ x, ‖addMarkovOp ν (F ∘ φ) x‖ ^ 2 ∂m ∧
      ∫ X, ‖F X‖ ^ 2 ∂(m.map φ) = ∫ x, ‖(F ∘ φ) x‖ ^ 2 ∂m := by
    intro F
    refine ⟨φ.measurableEmbedding.memLp_map_measure_iff, ?_, ?_, ?_⟩
    · rw [φ.measurableEmbedding.integral_map]
      rfl
    · rw [φ.measurableEmbedding.integral_map]
      simp only [markovOp_map_apply φ hφ]
    · rw [φ.measurableEmbedding.integral_map]
      rfl
  constructor
  · intro h f hf hmean
    have hF : (f ∘ φ.symm) ∘ φ = f := by
      funext x
      simp
    obtain ⟨k1, k2, k3, k4⟩ := key (f ∘ φ.symm)
    rw [hF] at k1 k2 k3 k4
    have := h (f ∘ φ.symm) (k1.mpr hf) (k2.trans hmean)
    rwa [k3, k4] at this
  · intro h F hF hmean
    obtain ⟨k1, k2, k3, k4⟩ := key F
    rw [k3, k4]
    exact h (F ∘ φ) (k1.mp hF) (k2.symm.trans hmean)

/-- Spectral gaps are transported by a measurable group isomorphism. -/
theorem isSpectralGap_map_iff (φ : A ≃ᵐ G) (hφ : ∀ x y, φ (x + y) = φ x * φ y)
    (m ν : Measure A) (γ : ℝ) :
    IsSpectralGap (m.map φ) (ν.map φ) γ ↔ IsAddSpectralGap m ν γ := by
  unfold IsSpectralGap IsAddSpectralGap
  have : {γ' | PoincareIneq (m.map φ) (ν.map φ) γ'} = {γ' | AddPoincareIneq m ν γ'} := by
    ext γ'
    exact poincareIneq_map_iff φ hφ m ν γ'
  rw [this]

end Transport

/-! ### The isomorphism `ℝ / 2πℤ ≃ SO(2)` -/

/-- The rotation by `θ` as an element of the group `SO(2)`. -/
noncomputable def rotSO (θ : ℝ) : SO 2 := ⟨rotMat θ, rotMat_mem θ⟩

theorem rotSO_add (θ φ : ℝ) : rotSO (θ + φ) = rotSO θ * rotSO φ :=
  Subtype.ext (rotMat_add θ φ)

theorem rotSO_eq_one_iff (θ : ℝ) : rotSO θ = 1 ↔ ∃ k : ℤ, (k : ℝ) * (2 * π) = θ := by
  rw [← rotMat_eq_one_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem rotSO_periodic : Function.Periodic rotSO (2 * π) := by
  intro θ
  rw [rotSO_add, (rotSO_eq_one_iff (2 * π)).mpr ⟨1, by simp⟩, mul_one]

theorem continuous_rotSO : Continuous rotSO := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [rotMat] <;> fun_prop

/-- The map `ℝ / 2πℤ → SO(2)` induced by `θ ↦ R_θ`. -/
noncomputable def circleToSO : AddCircle (2 * π) → SO 2 := rotSO_periodic.lift

@[simp] theorem circleToSO_coe (θ : ℝ) : circleToSO (θ : AddCircle (2 * π)) = rotSO θ := rfl

/-- `circleToSO` is a group homomorphism. -/
theorem circleToSO_add (x y : AddCircle (2 * π)) :
    circleToSO (x + y) = circleToSO x * circleToSO y := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact rotSO_add a b

theorem continuous_circleToSO : Continuous circleToSO :=
  continuous_rotSO.quotient_liftOn' _

theorem circleToSO_bijective : Function.Bijective circleToSO := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
    have h' : rotSO a = rotSO b := h
    have h1 : rotSO (-a + b) = 1 := by
      have h2 : rotSO (-a) * rotSO a = 1 := by
        rw [← rotSO_add, neg_add_cancel]
        exact (rotSO_eq_one_iff 0).mpr ⟨0, by simp⟩
      rw [rotSO_add, ← h', h2]
    obtain ⟨k, hk⟩ := (rotSO_eq_one_iff _).mp h1
    refine QuotientAddGroup.eq.mpr ?_
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨k, by rw [zsmul_eq_mul]; exact hk⟩
  · intro R
    obtain ⟨θ, hθ⟩ := exists_rotMat_eq R.2
    exact ⟨(θ : AddCircle (2 * π)), Subtype.ext hθ⟩

/-- **`ℝ / 2πℤ` and `SO(2)` are homeomorphic**, via `θ ↦ R_θ`. -/
noncomputable def circleHomeo : AddCircle (2 * π) ≃ₜ SO 2 :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective circleToSO circleToSO_bijective)
    continuous_circleToSO

@[simp] theorem circleHomeo_apply (x : AddCircle (2 * π)) : circleHomeo x = circleToSO x := rfl

/-- The same map as a measurable equivalence. -/
noncomputable def circleEquiv : AddCircle (2 * π) ≃ᵐ SO 2 := circleHomeo.toMeasurableEquiv

@[simp] theorem circleEquiv_apply (x : AddCircle (2 * π)) : circleEquiv x = circleToSO x := rfl

/-- **Haar measure of the circle is mapped to Haar measure of `SO(2)`.** -/
theorem map_circleToSO_haar :
    (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))).map circleEquiv = haarSO 2 := by
  set μ' := (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))).map circleEquiv with hμ'
  have hmeas : Measurable (circleEquiv : AddCircle (2 * π) → SO 2) := circleEquiv.measurable
  have : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have : μ'.IsMulLeftInvariant := by
    constructor
    intro g
    obtain ⟨y, rfl⟩ := circleToSO_bijective.2 g
    have h1 : (fun X : SO 2 => circleToSO y * X) ∘ circleEquiv
        = circleEquiv ∘ fun x : AddCircle (2 * π) => y + x := by
      funext x
      simp [circleToSO_add]
    rw [hμ', Measure.map_map (measurable_const_mul _) hmeas, h1,
      ← Measure.map_map hmeas (measurable_const_add y), map_add_left_eq_self]
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ' (haarSO 2)
  have huniv : μ' Set.univ = (Measure.haarScalarFactor μ' (haarSO 2) : ENNReal)
      * haarSO 2 Set.univ := by
    conv_lhs => rw [h]
    simp
  rw [measure_univ, measure_univ, mul_one] at huniv
  have hc : Measure.haarScalarFactor μ' (haarSO 2) = 1 := by exact_mod_cast huniv.symm
  rw [h, hc, one_smul]

/-! ### The sampler on the matrix group `SO(2)` -/

/-- The step distribution of the tangent-space sampler on the matrix group `SO(2)`: the law of
the rotation matrix `R_{θ(a)}` for `a ∼ N(0, v)`. -/
noncomputable def so2Step (v : ℝ≥0) : Measure (SO 2) :=
  (ProbabilityTheory.gaussianReal 0 v).map (fun a => rotSO (stepAngle a))

theorem so2Step_eq_map (v : ℝ≥0) : so2Step v = (gaussStep v).map circleEquiv := by
  rw [so2Step, gaussStep, circleStep, Measure.map_map circleEquiv.measurable
    measurable_coe_stepAngle]
  rfl

instance (v : ℝ≥0) : IsProbabilityMeasure (so2Step v) := by
  rw [so2Step_eq_map]
  exact Measure.isProbabilityMeasure_map circleEquiv.measurable.aemeasurable

/-- **Theorem (spectral gap on the matrix group `SO(2)`).** The walk `X ↦ X R_{θ(a)}` on `SO(2)`
with `a ∼ N(0, v)`, `v > 0`, has spectral gap exactly `1 - λ₁`. -/
theorem so2_isSpectralGap {v : ℝ≥0} (hv : v ≠ 0) :
    IsSpectralGap (haarSO 2) (so2Step v) (1 - gaussLam v) := by
  rw [so2Step_eq_map, ← map_circleToSO_haar]
  exact (isSpectralGap_map_iff circleEquiv circleToSO_add _ _ _).mpr (gauss_isSpectralGap hv)

/-- **Theorem (`L²` convergence rate on the matrix group `SO(2)`).** `λ₁` is the least `L²`
contraction coefficient of the walk on `SO(2)`. -/
theorem so2_isLeast_contraction {v : ℝ≥0} (hv : v ≠ 0) :
    IsLeast {ρ : ℝ | 0 ≤ ρ ∧ L2ContractionBound (haarSO 2) (so2Step v) ρ} (gaussLam v) := by
  have h := gauss_isLeast_contraction hv
  have hset : {ρ : ℝ | 0 ≤ ρ ∧ L2ContractionBound (haarSO 2) (so2Step v) ρ}
      = {ρ : ℝ | 0 ≤ ρ ∧ AddL2ContractionBound
          (AddCircle.haarAddCircle : Measure (AddCircle (2 * π))) (gaussStep v) ρ} := by
    ext ρ
    show (0 ≤ ρ ∧ _) ↔ (0 ≤ ρ ∧ _)
    rw [so2Step_eq_map, ← map_circleToSO_haar,
      l2ContractionBound_map_iff circleEquiv circleToSO_add]
  rw [hset]
  exact h

end SOnMCMC

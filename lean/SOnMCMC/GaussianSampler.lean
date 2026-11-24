import Mathlib.Probability.Distributions.Gaussian.Multivariate
import SOnMCMC.PrincipalRoot
import SOnMCMC.SO2Transport

/-!
# The Gaussian tangent-space sampler on `SO(n)`, concretely

Paper: Section 5.5.

This file constructs the sampler of Section 5 without hypotheses.

* The probability space is `ℝ^{i<j}` with independent standard Gaussians (`pairGauss n`).
* The tangent proposal is the skew-symmetric matrix `gaussTangent v x = √v · skewOf x`, whose
  entries below the diagonal are the coordinates; its law is invariant under conjugation by
  `O(n)` because the product Gaussian is rotation invariant (`pi_gaussian_map_of_isometry`).
* The group step is `gaussStepFun v x = principalStep (gaussTangent v x)`, and its law is
  `gaussSOStep n v`.

Main results:

* `gaussSOStep_conjInvariant`: the step distribution is conjugation invariant;
* `gaussSO_markovOp_entry`: matrix entries are eigenfunctions of the sampler;
* `gaussSO_gap_le`: the spectral gap of the sampler is at most `(n - 1) v`;
* `gaussSOStep_two`, `gaussSO_two_isSpectralGap`: for `n = 2` the sampler is the walk of
  Section 4, and its spectral gap is exactly `1 - λ₁`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace SOnMCMC

/-! ### Rotation invariance of the product Gaussian -/

/-- A linear map of `ℝ^ι` that preserves the Euclidean norm preserves the standard Gaussian
product measure. -/
theorem pi_gaussian_map_of_isometry {ι : Type*} [Fintype ι] (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hT : ∀ x, ∑ i, T x i ^ 2 = ∑ i, x i ^ 2) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map T
      = Measure.pi fun _ : ι => gaussianReal 0 1 := by
  set P := Measure.pi fun _ : ι => gaussianReal 0 1 with hP
  let e := WithLp.linearEquiv 2 ℝ (ι → ℝ)
  let Tl : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
    e.symm.toLinearMap ∘ₗ T ∘ₗ e.toLinearMap
  have hnorm : ∀ x, ‖Tl x‖ = ‖x‖ := by
    intro x
    have h1 : ‖Tl x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      exact hT (e x)
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  let li : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ ι := ⟨Tl, hnorm⟩
  let le := li.toLinearIsometryEquiv rfl
  have hstd := stdGaussian_map (E := EuclideanSpace ℝ ι) le
  have hpi : P.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ ι) := map_pi_eq_stdGaussian
  have hm : Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have hcomm : (le : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) ∘ WithLp.toLp 2
      = WithLp.toLp 2 ∘ T := by
    funext x
    rfl
  have key : (P.map T).map (MeasurableEquiv.toLp 2 (ι → ℝ))
      = P.map (MeasurableEquiv.toLp 2 (ι → ℝ)) := by
    rw [MeasurableEquiv.coe_toLp, Measure.map_map hm hTm, ← hcomm,
      ← Measure.map_map le.continuous.measurable hm, hpi, hstd]
  exact (MeasurableEquiv.toLp 2 (ι → ℝ)).map_measurableEquiv_injective key

/-! ### Skew-symmetric matrices in coordinates -/

variable {n : ℕ}

/-- The index set of the independent coordinates of a skew-symmetric matrix. -/
abbrev Pairs (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

/-- The skew-symmetric matrix with entry `x (i, j)` in position `(j, i)` for `i < j`. -/
def skewOf (x : Pairs n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if h : i < j then -x ⟨(i, j), h⟩ else if h : j < i then x ⟨(j, i), h⟩ else 0

/-- The entries of a matrix below the diagonal. -/
def lowerCoords (M : Matrix (Fin n) (Fin n) ℝ) : Pairs n → ℝ := fun p => M p.1.2 p.1.1

theorem skewOf_apply_lt (x : Pairs n → ℝ) {i j : Fin n} (h : i < j) :
    skewOf x i j = -x ⟨(i, j), h⟩ := by
  simp [skewOf, h]

theorem skewOf_apply_gt (x : Pairs n → ℝ) {i j : Fin n} (h : j < i) :
    skewOf x i j = x ⟨(j, i), h⟩ := by
  simp [skewOf, h, not_lt.mpr h.le]

theorem skewOf_apply_self (x : Pairs n → ℝ) (i : Fin n) : skewOf x i i = 0 := by
  simp [skewOf]

theorem transpose_skewOf (x : Pairs n → ℝ) : (skewOf x)ᵀ = -skewOf x := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [skewOf_apply_lt x h, skewOf_apply_gt x h]
  · subst h
    simp [skewOf_apply_self]
  · simp [skewOf_apply_lt x h, skewOf_apply_gt x h]

theorem lowerCoords_skewOf (x : Pairs n → ℝ) : lowerCoords (skewOf x) = x := by
  funext p
  exact skewOf_apply_gt x p.2

theorem skewOf_lowerCoords {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = -M) :
    skewOf (lowerCoords M) = M := by
  have hji : ∀ i j, M j i = -M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa using this
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [skewOf_apply_lt _ h]
    simp [lowerCoords, hji i j]
  · subst h
    rw [skewOf_apply_self]
    have := hji i i
    linarith
  · rw [skewOf_apply_gt _ h]
    rfl

theorem skewOf_add (x y : Pairs n → ℝ) : skewOf (x + y) = skewOf x + skewOf y := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [skewOf_apply_lt _ h]
    ring
  · subst h
    simp [skewOf_apply_self]
  · simp [skewOf_apply_gt _ h]

theorem skewOf_smul (c : ℝ) (x : Pairs n → ℝ) : skewOf (c • x) = c • skewOf x := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [skewOf_apply_lt _ h]
  · subst h
    simp [skewOf_apply_self]
  · simp [skewOf_apply_gt _ h]

theorem frobSq_transpose' (M : Matrix (Fin n) (Fin n) ℝ) : frobSq Mᵀ = frobSq M := by
  simp only [frobSq, transpose_apply]
  exact Finset.sum_comm

/-- `‖skewOf x‖² = 2 ∑ x_p²`. -/
theorem frobSq_skewOf (x : Pairs n → ℝ) : frobSq (skewOf x) = 2 * ∑ p, x p ^ 2 := by
  have h1 : ∀ i j : Fin n, skewOf x i j ^ 2
      = (if h : i < j then x ⟨(i, j), h⟩ ^ 2 else 0)
        + (if h : j < i then x ⟨(j, i), h⟩ ^ 2 else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [skewOf_apply_lt x h, h, not_lt.mpr h.le]
    · subst h
      simp [skewOf_apply_self]
    · simp [skewOf_apply_gt x h, h, not_lt.mpr h.le]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, (if h : i < j then x ⟨(i, j), h⟩ ^ 2 else 0)
      = ∑ p, x p ^ 2 := by
    set F : Fin n × Fin n → ℝ := fun q => if h : q.1 < q.2 then x ⟨q, h⟩ ^ 2 else 0 with hF
    have e1 : ∑ i : Fin n, ∑ j : Fin n, (if h : i < j then x ⟨(i, j), h⟩ ^ 2 else 0)
        = ∑ q : Fin n × Fin n, F q := (Fintype.sum_prod_type' (f := fun i j => F (i, j))).symm
    have e2 : ∑ q : Fin n × Fin n, F q
        = ∑ q ∈ Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2), F q := by
      refine (Finset.sum_filter_of_ne fun q _ hq => ?_).symm
      by_contra hlt
      exact hq (by simp [hF, hlt])
    have e3 : ∑ q ∈ Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2), F q
        = ∑ p : Pairs n, F p :=
      Finset.sum_subtype _ (by simp) F
    rw [e1, e2, e3]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [hF, p.2]
  have h3 : ∑ i : Fin n, ∑ j : Fin n, (if h : j < i then x ⟨(j, i), h⟩ ^ 2 else 0)
      = ∑ p, x p ^ 2 := by
    rw [Finset.sum_comm]
    exact h2
  simp only [frobSq, h1, Finset.sum_add_distrib]
  rw [h2, h3]
  ring

/-- Conjugation by `Q`, in the coordinates of skew-symmetric matrices. -/
def conjCoords (Q : Matrix (Fin n) (Fin n) ℝ) : (Pairs n → ℝ) →ₗ[ℝ] (Pairs n → ℝ) where
  toFun x := lowerCoords (Q * skewOf x * Qᵀ)
  map_add' x y := by
    funext p
    simp [lowerCoords, skewOf_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by
    funext p
    simp [lowerCoords, skewOf_smul]

theorem skewOf_conjCoords (Q : Matrix (Fin n) (Fin n) ℝ) (x : Pairs n → ℝ) :
    skewOf (conjCoords Q x) = Q * skewOf x * Qᵀ := by
  show skewOf (lowerCoords (Q * skewOf x * Qᵀ)) = Q * skewOf x * Qᵀ
  refine skewOf_lowerCoords ?_
  simp only [transpose_mul, transpose_transpose, transpose_skewOf, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_assoc]

theorem sum_sq_conjCoords {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q ∈ orthogonalGroup (Fin n) ℝ)
    (x : Pairs n → ℝ) : ∑ p, conjCoords Q x p ^ 2 = ∑ p, x p ^ 2 := by
  have h1 := frobSq_skewOf (conjCoords Q x)
  have h2 := frobSq_skewOf x
  have h3 : frobSq (Q * skewOf x * Qᵀ) = frobSq (skewOf x) := by
    rw [Matrix.mul_assoc, frobSq_orthogonal_mul hQ, ← frobSq_transpose', transpose_mul,
      transpose_transpose, frobSq_orthogonal_mul hQ, frobSq_transpose']
  rw [skewOf_conjCoords, h3, h2] at h1
  linarith

/-! ### The sampler -/

/-- The probability space of the sampler: independent standard Gaussians indexed by the pairs
`i < j`. -/
noncomputable abbrev pairGauss (n : ℕ) : Measure (Pairs n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- The Gaussian tangent proposal with coordinate variance `v`. -/
noncomputable def gaussTangent (v : ℝ≥0) (x : Pairs n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Real.sqrt v • skewOf x

/-- The group step of the sampler: the principal projection of the tangent proposal, or the
identity if there is none. -/
noncomputable def gaussStepFun (v : ℝ≥0) (x : Pairs n → ℝ) : SO n :=
  ⟨principalStep (gaussTangent v x), principalStep_mem _⟩

/-- **The step distribution of the Gaussian tangent-space sampler on `SO(n)`.** -/
noncomputable def gaussSOStep (n : ℕ) (v : ℝ≥0) : Measure (SO n) :=
  (pairGauss n).map (gaussStepFun v)

theorem transpose_gaussTangent (v : ℝ≥0) (x : Pairs n → ℝ) :
    (gaussTangent v x)ᵀ = -gaussTangent v x := by
  simp [gaussTangent, transpose_smul, transpose_skewOf]

theorem continuous_gaussTangent (v : ℝ≥0) :
    Continuous (gaussTangent v : (Pairs n → ℝ) → Matrix (Fin n) (Fin n) ℝ) := by
  refine continuous_matrix fun i j => ?_
  simp only [gaussTangent, Matrix.smul_apply, smul_eq_mul]
  rcases lt_trichotomy i j with h | h | h
  · simp only [skewOf_apply_lt _ h]
    exact continuous_const.mul (continuous_apply _).neg
  · subst h
    simp only [skewOf_apply_self]
    exact continuous_const
  · simp only [skewOf_apply_gt _ h]
    exact continuous_const.mul (continuous_apply _)

theorem measurable_gaussStepFun (v : ℝ≥0) :
    Measurable (gaussStepFun v : (Pairs n → ℝ) → SO n) :=
  (measurable_principalStep.comp (continuous_gaussTangent v).measurable).subtype_mk

instance (n : ℕ) (v : ℝ≥0) : IsProbabilityMeasure (gaussSOStep n v) :=
  Measure.isProbabilityMeasure_map (measurable_gaussStepFun v).aemeasurable

/-- For every outcome the step is a rejection or the principal projection of the proposal. -/
theorem gaussStepFun_spec (v : ℝ≥0) (x : Pairs n → ℝ) :
    gaussStepFun v x = 1 ∨
      (skewPart (gaussStepFun v x : Matrix (Fin n) (Fin n) ℝ) = gaussTangent v x ∧
        (symPart (gaussStepFun v x : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) := by
  by_cases hB : (1 + gaussTangent v x * gaussTangent v x).PosSemidef
  · right
    obtain ⟨_, h2, h3⟩ := principalStep_spec (transpose_gaussTangent v x) hB
    exact ⟨h2, h3⟩
  · left
    exact Subtype.ext (principalStep_of_not fun h => hB h.2)

/-- **The step distribution of the Gaussian sampler is conjugation invariant.** -/
theorem gaussSOStep_conjInvariant (n : ℕ) (v : ℝ≥0) : ConjInvariant (gaussSOStep n v) := by
  intro Q
  have hcomp : conjO Q ∘ gaussStepFun v
      = gaussStepFun v ∘ conjCoords (Q : Matrix (Fin n) (Fin n) ℝ) := by
    funext x
    refine Subtype.ext ?_
    show (Q : Matrix (Fin n) (Fin n) ℝ) * principalStep (gaussTangent v x)
        * (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ
      = principalStep (gaussTangent v (conjCoords (Q : Matrix (Fin n) (Fin n) ℝ) x))
    rw [← principalStep_conj Q.2]
    congr 1
    simp only [gaussTangent, skewOf_conjCoords, Matrix.mul_smul, Matrix.smul_mul]
  rw [gaussSOStep, Measure.map_map (continuous_conjO Q).measurable (measurable_gaussStepFun v),
    hcomp, ← Measure.map_map (measurable_gaussStepFun v)
      (conjCoords (Q : Matrix (Fin n) (Fin n) ℝ)).continuous_of_finiteDimensional.measurable,
    pi_gaussian_map_of_isometry _ (sum_sq_conjCoords Q.2)]

/-! ### Moments of the proposal -/

theorem integrable_coord_sq (p : Pairs n) :
    Integrable (fun x : Pairs n → ℝ => x p ^ 2) (pairGauss n) := by
  have hmp := measurePreserving_eval (μ := fun _ : Pairs n => gaussianReal 0 1) p
  exact hmp.integrable_comp_of_integrable (integrable_sq_gaussianReal 1)

theorem integral_coord_sq (p : Pairs n) : ∫ x : Pairs n → ℝ, x p ^ 2 ∂(pairGauss n) = 1 := by
  have hmp := measurePreserving_eval (μ := fun _ : Pairs n => gaussianReal 0 1) p
  have h : ∫ a : ℝ, a ^ 2 ∂(Measure.map (Function.eval p) (pairGauss n))
      = ∫ x : Pairs n → ℝ, x p ^ 2 ∂(pairGauss n) :=
    integral_map hmp.aemeasurable
      (by fun_prop : Measurable fun a : ℝ => a ^ 2).aestronglyMeasurable
  rw [← h, hmp.map_eq, integral_sq_gaussianReal]
  simp

/-- The squared entries of the proposal: `A_{ij}² = v x_p²` for the pair `p = {i, j}`. -/
theorem gaussTangent_sq (v : ℝ≥0) {i j : Fin n} (hij : i ≠ j) :
    ∃ p : Pairs n, ∀ x : Pairs n → ℝ, gaussTangent v x i j ^ 2 = v * x p ^ 2 := by
  have hv : Real.sqrt v ^ 2 = v := Real.sq_sqrt (NNReal.coe_nonneg v)
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨⟨(i, j), h⟩, fun x => ?_⟩
    simp only [gaussTangent, Matrix.smul_apply, smul_eq_mul, skewOf_apply_lt x h]
    rw [mul_pow, hv]
    ring
  · refine ⟨⟨(j, i), h⟩, fun x => ?_⟩
    simp only [gaussTangent, Matrix.smul_apply, smul_eq_mul, skewOf_apply_gt x h]
    rw [mul_pow, hv]

theorem integrable_gaussTangent_sq (v : ℝ≥0) (i j : Fin n) :
    Integrable (fun x : Pairs n → ℝ => gaussTangent v x i j ^ 2) (pairGauss n) := by
  by_cases hij : i = j
  · subst hij
    simp [gaussTangent, skewOf_apply_self]
  · obtain ⟨p, hp⟩ := gaussTangent_sq v hij
    simp only [hp]
    exact (integrable_coord_sq p).const_mul _

/-- The off-diagonal entries of the proposal have second moment `v`. -/
theorem integral_gaussTangent_sq (v : ℝ≥0) (i j : Fin n) (hij : i ≠ j) :
    ∫ x : Pairs n → ℝ, gaussTangent v x i j ^ 2 ∂(pairGauss n) = Real.sqrt v ^ 2 := by
  obtain ⟨p, hp⟩ := gaussTangent_sq v hij
  simp only [hp]
  rw [integral_const_mul, integral_coord_sq, mul_one, Real.sq_sqrt (NNReal.coe_nonneg v)]

/-! ### Theorems for the concrete sampler -/

/-- **Matrix entries are eigenfunctions of the Gaussian sampler**, with eigenvalue
`λ = E[tr R] / n`. -/
theorem gaussSO_markovOp_entry (n : ℕ) [NeZero n] (v : ℝ≥0) (i j : Fin n) :
    markovOp (gaussSOStep n v) (fun X : SO n => (X : Matrix (Fin n) (Fin n) ℝ) i j)
      = fun X : SO n => stdEig (gaussSOStep n v) * (X : Matrix (Fin n) (Fin n) ℝ) i j :=
  markovOp_entry _ (gaussSOStep_conjInvariant n v) i j

/-- **Theorem (the Gaussian sampler on `SO(n)`).** For `n ≥ 2` and coordinate variance `v`, every
Poincaré constant of the Gaussian tangent-space sampler with principal projection is at most
`(n - 1) v`: its spectral gap is at most `(n - 1) σ²`.  No hypotheses remain: the proposal, the
projection and the step distribution are the ones constructed in this file. -/
theorem gaussSO_gap_le {n : ℕ} (hn : 2 ≤ n) (v : ℝ≥0) {γ : ℝ}
    (hγ : PoincareIneq (haarSO n) (gaussSOStep n v) γ) : γ ≤ (n - 1) * v := by
  have h := sampler_gap_le (pairGauss n) hn (measurable_gaussStepFun v) (gaussStepFun_spec v)
    (σ := Real.sqrt v) (transpose_gaussTangent v) (integrable_gaussTangent_sq v)
    (integral_gaussTangent_sq v) (gaussSOStep_conjInvariant n v) hγ
  rwa [Real.sq_sqrt (NNReal.coe_nonneg v)] at h

/-- The spectral gap of the Gaussian sampler is at most `1 - λ`. -/
theorem gaussSO_gap_le_one_sub_stdEig {n : ℕ} (hn : 2 ≤ n) (v : ℝ≥0) {γ : ℝ}
    (hγ : PoincareIneq (haarSO n) (gaussSOStep n v) γ) : γ ≤ 1 - stdEig (gaussSOStep n v) :=
  gap_le_of_conjInvariant hn _ (gaussSOStep_conjInvariant n v) hγ

/-! ### Dimension two -/

/-- The unique pair `0 < 1` when `n = 2`. -/
def pair01 : Pairs 2 := ⟨(0, 1), by decide⟩

theorem skewOf_two (x : Pairs 2 → ℝ) : skewOf x = skew2 (x pair01) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew2, skewOf, pair01]

theorem transpose_skew2 (a : ℝ) : (skew2 a)ᵀ = -skew2 a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew2]

/-- In dimension two the group step is the rotation by the step angle. -/
theorem principalStep_skew2 (a : ℝ) : principalStep (skew2 a) = rotMat (stepAngle a) := by
  by_cases h : |a| ≤ 1
  · obtain ⟨h1, h2⟩ := principal_step_two h
    exact (eq_principalStep (transpose_skew2 a)
      (mem_specialOrthogonalGroup_iff.mp (rotMat_mem _)).1 h1 h2).symm
  · have h' : 1 < |a| := not_le.mp h
    rw [rotMat_stepAngle_of_lt h']
    refine principalStep_of_not fun hc => h ?_
    obtain ⟨o1, o2, _⟩ := principalStep_spec hc.1 hc.2
    exact abs_le_one_of_skewPart_eq o1 o2

/-- **For `n = 2` the general sampler is the walk of Section 4.** -/
theorem gaussSOStep_two (v : ℝ≥0) : gaussSOStep 2 v = so2Step v := by
  have hfun : (gaussStepFun v : (Pairs 2 → ℝ) → SO 2)
      = (fun a : ℝ => rotSO (stepAngle (Real.sqrt v * a))) ∘ Function.eval pair01 := by
    funext x
    refine Subtype.ext ?_
    show principalStep (gaussTangent v x) = rotMat (stepAngle (Real.sqrt v * x pair01))
    rw [← principalStep_skew2]
    congr 1
    rw [gaussTangent, skewOf_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew2]
  have hmp := measurePreserving_eval (μ := fun _ : Pairs 2 => gaussianReal 0 1) pair01
  have hscale : (gaussianReal 0 1).map (fun a : ℝ => Real.sqrt v * a) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  have hmeas : Measurable fun a : ℝ => rotSO (stepAngle a) :=
    continuous_rotSO.measurable.comp measurable_stepAngle
  have hF : (fun a : ℝ => rotSO (stepAngle (Real.sqrt v * a)))
      = (fun a => rotSO (stepAngle a)) ∘ fun a : ℝ => Real.sqrt v * a := rfl
  have hmeasF : Measurable fun a : ℝ => rotSO (stepAngle (Real.sqrt v * a)) :=
    hmeas.comp (measurable_const_mul _)
  rw [gaussSOStep, hfun, ← Measure.map_map hmeasF (measurable_pi_apply pair01), hmp.map_eq, hF,
    ← Measure.map_map hmeas (measurable_const_mul _), hscale]
  rfl

/-- **Theorem (the Gaussian sampler on `SO(2)`).** For `n = 2` the spectral gap of the Gaussian
tangent-space sampler with principal projection is exactly `1 - λ₁`. -/
theorem gaussSO_two_isSpectralGap {v : ℝ≥0} (hv : v ≠ 0) :
    IsSpectralGap (haarSO 2) (gaussSOStep 2 v) (1 - gaussLam v) := by
  rw [gaussSOStep_two]
  exact so2_isSpectralGap hv

/-- For `n = 2`, `λ₁` is the least `L²` contraction coefficient of the Gaussian sampler. -/
theorem gaussSO_two_isLeast_contraction {v : ℝ≥0} (hv : v ≠ 0) :
    IsLeast {ρ : ℝ | 0 ≤ ρ ∧ L2ContractionBound (haarSO 2) (gaussSOStep 2 v) ρ}
      (gaussLam v) := by
  rw [gaussSOStep_two]
  exact so2_isLeast_contraction hv

end SOnMCMC

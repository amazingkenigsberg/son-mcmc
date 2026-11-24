import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Topology.UniformSpace.Uniformizable
import SOnMCMC.CompactWalk
import SOnMCMC.Projection

/-!
# Random walks on `SO(n)` with conjugation-invariant steps

Paper: Sections 5.2–5.3.

* `SO n` is a compact topological group; `haarSO n` is its normalised Haar measure, which is
  left- and right-invariant.
* For a step distribution `ν` invariant under conjugation by `O(n)`, the Fourier transform at
  the standard representation is scalar, `∫ R dν = λ · 1` with `λ = E[tr R] / n`
  (`fourierMat_std_eq`).
* Hence every matrix entry `X ↦ Xᵢⱼ` is an eigenfunction of the walk with eigenvalue `λ`
  (`markovOp_entry`), it has Haar mean zero for `n ≥ 2` (`integral_entry_haar`), and therefore the
  spectral gap is at most `1 - λ` (`gap_le_of_conjInvariant`).
* `1 - λ = E‖1 - R‖² / (2n)` (`one_sub_stdEig_eq_frob`), and for the tangent-space sampler with
  principal projection `E[‖A‖²; accepted] / (2n) ≤ 1 - λ ≤ E‖A‖² / n`
  (`one_sub_stdEig_ge`, `one_sub_stdEig_le_of_step`).
* For tangent proposals whose off-diagonal coordinates have second moment `σ²`, the spectral gap
  is at most `(n - 1) σ²` (`sampler_gap_le`).
-/

open MeasureTheory Matrix

namespace SOnMCMC

/-- The special orthogonal group `SO(n)` of real `n × n` matrices. -/
abbrev SO (n : ℕ) : Type := specialOrthogonalGroup (Fin n) ℝ

variable {n : ℕ}

theorem SO.coe_mem_orthogonal (R : SO n) :
    (R : Matrix (Fin n) (Fin n) ℝ) ∈ orthogonalGroup (Fin n) ℝ :=
  (mem_specialOrthogonalGroup_iff.mp R.2).1

/-! ### Topology and Haar measure -/

instance SO.instSecondCountableTopology : SecondCountableTopology (SO n) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  exact TopologicalSpace.Subtype.secondCountableTopology _

/-- `SO(n)` is a topological group. -/
instance SO.instIsTopologicalGroup : IsTopologicalGroup (SO n) where
  continuous_inv := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_subtype_val.matrix_transpose

/-- `SO(n)` is compact: it is a closed subset of the cube `[-1, 1]^{n × n}`. -/
instance SO.instCompactSpace : CompactSpace (SO n) := by
  have hK : IsCompact {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1} := by
    have : {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1}
        = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
            (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) := by
      ext A
      constructor
      · intro h i _ j _
        exact h i j
      · intro h i j
        exact h i (Set.mem_univ _) j (Set.mem_univ _)
    rw [this]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hclosed : IsClosed (specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
    have : (specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ))
        = {A | A * Aᵀ = 1} ∩ {A | A.det = 1} := by
      ext A
      simp [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
    rw [this]
    exact (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_transpose)
      continuous_const).inter (isClosed_eq continuous_id.matrix_det continuous_const)
  have hsub : (specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ))
      ⊆ {A | ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1} := by
    intro A hA i j
    have hU : A ∈ unitaryGroup (Fin n) ℝ := (mem_specialOrthogonalGroup_iff.mp hA).1
    have := entry_norm_bound_of_unitary hU i j
    rwa [Real.norm_eq_abs, abs_le] at this
  exact isCompact_iff_compactSpace.mp (hK.of_isClosed_subset hclosed hsub)

/-- Normalised Haar measure on `SO(n)`. -/
noncomputable def haarSO (n : ℕ) : Measure (SO n) := Measure.haarMeasure ⊤

instance haarSO.instIsHaarMeasure : (haarSO n).IsHaarMeasure := by
  unfold haarSO
  infer_instance

instance haarSO.instIsProbabilityMeasure : IsProbabilityMeasure (haarSO n) :=
  ⟨Measure.haarMeasure_self⟩

instance haarSO.instIsMulRightInvariant : (haarSO n).IsMulRightInvariant :=
  isMulRightInvariant_of_compact _

/-! ### The standard representation -/

/-- The standard representation of `SO(n)` on `ℝⁿ`: the inclusion into matrices. -/
def stdRep (n : ℕ) : SO n →* Matrix (Fin n) (Fin n) ℝ where
  toFun R := (R : Matrix (Fin n) (Fin n) ℝ)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem stdRep_apply (R : SO n) : stdRep n R = (R : Matrix (Fin n) (Fin n) ℝ) := rfl

theorem continuous_entry (i j : Fin n) :
    Continuous fun R : SO n => (R : Matrix (Fin n) (Fin n) ℝ) i j :=
  continuous_subtype_val.matrix_elem i j

theorem abs_entry_le_one (R : SO n) (i j : Fin n) :
    |(R : Matrix (Fin n) (Fin n) ℝ) i j| ≤ 1 := by
  have := entry_norm_bound_of_unitary (SO.coe_mem_orthogonal R) i j
  rwa [Real.norm_eq_abs] at this

theorem integrable_entry (ν : Measure (SO n)) [IsFiniteMeasure ν] (i j : Fin n) :
    Integrable (fun R : SO n => (R : Matrix (Fin n) (Fin n) ℝ) i j) ν :=
  Integrable.of_bound (continuous_entry i j).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun R => abs_entry_le_one R i j)

theorem memLp_entry (ν : Measure (SO n)) [IsFiniteMeasure ν] (i j : Fin n) :
    MemLp (fun R : SO n => (R : Matrix (Fin n) (Fin n) ℝ) i j) 2 ν :=
  MemLp.of_bound (continuous_entry i j).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun R => abs_entry_le_one R i j)

theorem integrable_trace (ν : Measure (SO n)) [IsFiniteMeasure ν] :
    Integrable (fun R : SO n => (R : Matrix (Fin n) (Fin n) ℝ).trace) ν := by
  simp only [trace, diag_apply]
  exact integrable_finsetSum _ fun i _ => integrable_entry ν i i

/-! ### Conjugation invariance -/

/-- Conjugation of `SO(n)` by an orthogonal matrix `Q`: `R ↦ Q R Qᵀ`. -/
def conjO (Q : orthogonalGroup (Fin n) ℝ) (R : SO n) : SO n :=
  ⟨(Q : Matrix (Fin n) (Fin n) ℝ) * R * (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ, by
    have hQ := Q.2
    have hQ1 := (mem_orthogonalGroup_iff (Fin n) ℝ).mp hQ
    have hR := mem_specialOrthogonalGroup_iff.mp R.2
    rw [mem_specialOrthogonalGroup_iff]
    constructor
    · have hQt : (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ ∈ orthogonalGroup (Fin n) ℝ := by
        rw [mem_orthogonalGroup_iff, transpose_transpose]
        exact (mem_orthogonalGroup_iff' (Fin n) ℝ).mp hQ
      exact mul_mem (mul_mem hQ hR.1) hQt
    · rw [det_mul, det_mul, det_transpose, hR.2, mul_one]
      have := congrArg det hQ1
      rwa [det_mul, det_transpose, det_one] at this⟩

@[simp] theorem coe_conjO (Q : orthogonalGroup (Fin n) ℝ) (R : SO n) :
    (conjO Q R : Matrix (Fin n) (Fin n) ℝ)
      = (Q : Matrix (Fin n) (Fin n) ℝ) * R * (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ := rfl

theorem continuous_conjO (Q : orthogonalGroup (Fin n) ℝ) : Continuous (conjO Q) :=
  Continuous.subtype_mk
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

/-- A step distribution on `SO(n)` is *conjugation invariant* if it is preserved by
`R ↦ Q R Qᵀ` for every orthogonal `Q`. -/
def ConjInvariant (ν : Measure (SO n)) : Prop :=
  ∀ Q : orthogonalGroup (Fin n) ℝ, ν.map (conjO Q) = ν

/-- The mean step `∫ R dν` commutes with conjugation by every orthogonal matrix. -/
theorem fourierMat_std_conj (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    (Q : orthogonalGroup (Fin n) ℝ) :
    fourierMat ν (stdRep n)
      = (Q : Matrix (Fin n) (Fin n) ℝ) * fourierMat ν (stdRep n)
          * (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ :=
  fourierMat_eq_conj ν (stdRep n) (integrable_entry ν) (conjO Q)
    ⟨(continuous_conjO Q).measurable, hν Q⟩ _ _ (fun _ => rfl)

/-- The reflection `diag(1, …, -1, …, 1)` with `-1` in position `i`. -/
def flipMat (i : Fin n) : Matrix (Fin n) (Fin n) ℝ := diagonal (fun k => if k = i then -1 else 1)

theorem flipMat_mem (i : Fin n) : flipMat i ∈ orthogonalGroup (Fin n) ℝ := by
  rw [mem_orthogonalGroup_iff, flipMat, diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext k
  split_ifs <;> simp

theorem det_flipMat (i : Fin n) : (flipMat i).det = -1 := by
  rw [flipMat, det_diagonal, Finset.prod_ite_eq']
  simp

theorem swap_mem (i j : Fin n) :
    (Equiv.swap i j).permMatrix ℝ ∈ orthogonalGroup (Fin n) ℝ := by
  rw [mem_orthogonalGroup_iff, transpose_permMatrix, ← permMatrix_mul]
  simp

theorem fourierMat_std_offdiag (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    {i j : Fin n} (hij : i ≠ j) : fourierMat ν (stdRep n) i j = 0 := by
  have h := congrFun (congrFun (fourierMat_std_conj ν hν ⟨flipMat i, flipMat_mem i⟩) i) j
  simp only [flipMat, diagonal_transpose, mul_diagonal, diagonal_mul, ↓reduceIte,
    hij.symm] at h
  linarith

theorem fourierMat_std_diag (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    (i j : Fin n) : fourierMat ν (stdRep n) i i = fourierMat ν (stdRep n) j j := by
  have h := congrFun (congrFun
    (fourierMat_std_conj ν hν ⟨(Equiv.swap i j).permMatrix ℝ, swap_mem i j⟩) i) i
  simp only [transpose_permMatrix] at h
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv] at h
  simpa using h

/-- **The eigenvalue of the standard representation:** `λ(ν) = E[tr R] / n`. -/
noncomputable def stdEig (ν : Measure (SO n)) : ℝ :=
  (∫ R : SO n, (R : Matrix (Fin n) (Fin n) ℝ).trace ∂ν) / n

/-- **Schur's lemma for the standard representation, by hand.** For a conjugation-invariant
step distribution, `∫ R dν = λ · 1`. -/
theorem fourierMat_std_eq (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    [NeZero n] : fourierMat ν (stdRep n) = stdEig ν • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have htr : (fourierMat ν (stdRep n)).trace
      = ∫ R : SO n, (R : Matrix (Fin n) (Fin n) ℝ).trace ∂ν := by
    simp only [trace, diag_apply, fourierMat_apply, stdRep_apply]
    rw [integral_finsetSum _ (fun i _ => integrable_entry ν i i)]
  ext i j
  by_cases hij : i = j
  · subst hij
    have hall : ∀ k, fourierMat ν (stdRep n) k k = fourierMat ν (stdRep n) i i := fun k =>
      fourierMat_std_diag ν hν k i
    have htr' : (fourierMat ν (stdRep n)).trace = n * fourierMat ν (stdRep n) i i := by
      simp only [trace, diag_apply, hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, stdEig, ← htr, htr']
    field_simp
  · rw [fourierMat_std_offdiag ν hν hij, Matrix.smul_apply, one_apply_ne hij, smul_zero]

/-- **Matrix entries are eigenfunctions.** For a conjugation-invariant step distribution, each
coordinate function `X ↦ Xᵢⱼ` on `SO(n)` satisfies `P Xᵢⱼ = λ Xᵢⱼ`. -/
theorem markovOp_entry (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    [NeZero n] (i j : Fin n) :
    markovOp ν (fun X : SO n => (X : Matrix (Fin n) (Fin n) ℝ) i j)
      = fun X : SO n => stdEig ν * (X : Matrix (Fin n) (Fin n) ℝ) i j := by
  have := markovOp_matrixCoeff ν (stdRep n) (integrable_entry ν) i j
  rw [fourierMat_std_eq ν hν] at this
  simpa [mul_comm] using this

/-- Iterating: `Pᵗ Xᵢⱼ = λᵗ Xᵢⱼ`, so linear observables decorrelate at the exact rate `λ`. -/
theorem iterate_markovOp_entry (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    [NeZero n] (i j : Fin n) (t : ℕ) :
    (markovOp ν)^[t] (fun X : SO n => (X : Matrix (Fin n) (Fin n) ℝ) i j)
      = fun X : SO n => stdEig ν ^ t * (X : Matrix (Fin n) (Fin n) ℝ) i j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    funext X
    have h := congrFun (markovOp_entry ν hν i j) X
    simp only [markovOp] at h ⊢
    rw [integral_const_mul, h]
    ring

/-! ### Haar mean and norm of the matrix entries -/

/-- For `n ≥ 2` the matrix entries have Haar mean zero. -/
theorem integral_entry_haar (hn : 2 ≤ n) (i j : Fin n) :
    ∫ X : SO n, (X : Matrix (Fin n) (Fin n) ℝ) i j ∂(haarSO n) = 0 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨k, hk⟩ := exists_ne i
  have hmem : flipMat i * flipMat k ∈ specialOrthogonalGroup (Fin n) ℝ := by
    rw [mem_specialOrthogonalGroup_iff]
    refine ⟨mul_mem (flipMat_mem i) (flipMat_mem k), ?_⟩
    rw [det_mul, det_flipMat, det_flipMat]
    norm_num
  refine integral_eq_zero_of_mul_left_eq_neg (g := (⟨flipMat i * flipMat k, hmem⟩ : SO n))
    (fun X => ?_)
  show ((flipMat i * flipMat k) * (X : Matrix (Fin n) (Fin n) ℝ)) i j
    = -((X : Matrix (Fin n) (Fin n) ℝ) i j)
  rw [mul_assoc]
  have hik : ¬ i = k := fun h => hk h.symm
  simp only [flipMat, diagonal_mul, ↓reduceIte, hik]
  ring

/-- Each row of a rotation matrix is a unit vector. -/
theorem sum_sq_row (X : SO n) (i : Fin n) :
    ∑ j, (X : Matrix (Fin n) (Fin n) ℝ) i j ^ 2 = 1 := by
  have h := congrFun (congrFun
    ((mem_orthogonalGroup_iff (Fin n) ℝ).mp (SO.coe_mem_orthogonal X)) i) i
  simp only [mul_apply, transpose_apply, one_apply_eq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Some matrix entry has positive `L²(Haar)` norm. -/
theorem exists_entry_sq_pos [NeZero n] :
    ∃ j : Fin n, 0 < ∫ X : SO n, (X : Matrix (Fin n) (Fin n) ℝ) 0 j ^ 2 ∂(haarSO n) := by
  by_contra h
  push Not at h
  have hsum : ∑ j, ∫ X : SO n, (X : Matrix (Fin n) (Fin n) ℝ) 0 j ^ 2 ∂(haarSO n) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => (memLp_entry (haarSO n) 0 j).integrable_sq)]
    simp only [sum_sq_row]
    simp
  have : ∑ j, ∫ X : SO n, (X : Matrix (Fin n) (Fin n) ℝ) 0 j ^ 2 ∂(haarSO n) ≤ 0 :=
    Finset.sum_nonpos fun j _ => h j
  linarith

/-- **Theorem (upper bound on the spectral gap on `SO(n)`).** For `n ≥ 2` and a
conjugation-invariant step distribution `ν`, every Poincaré constant of the walk is at most
`1 - λ(ν)`: the spectral gap is at most `1 - E[tr R]/n`. -/
theorem gap_le_of_conjInvariant (hn : 2 ≤ n) (ν : Measure (SO n)) [IsProbabilityMeasure ν]
    (hν : ConjInvariant ν) {γ : ℝ} (hγ : PoincareIneq (haarSO n) ν γ) : γ ≤ 1 - stdEig ν := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨j, hj⟩ := exists_entry_sq_pos (n := n)
  exact hγ.le_of_eigenfunction (memLp_entry (haarSO n) 0 j) (integral_entry_haar hn 0 j) hj
    (markovOp_entry ν hν 0 j)

/-! ### The size of `1 - λ` -/

/-- `1 - λ = E[n - tr R] / n`. -/
theorem one_sub_stdEig (ν : Measure (SO n)) [IsProbabilityMeasure ν] [NeZero n] :
    1 - stdEig ν = (∫ R : SO n, ((n : ℝ) - (R : Matrix (Fin n) (Fin n) ℝ).trace) ∂ν) / n := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [integral_sub (integrable_const _) (integrable_trace ν), integral_const, probReal_univ,
    one_smul, stdEig]
  field_simp

/-- **`1 - λ` is the mean squared displacement:** `1 - λ = E‖1 - R‖² / (2n)`. -/
theorem one_sub_stdEig_eq_frob (ν : Measure (SO n)) [IsProbabilityMeasure ν] [NeZero n] :
    1 - stdEig ν
      = (∫ R : SO n, frobSq (1 - (R : Matrix (Fin n) (Fin n) ℝ)) ∂ν) / (2 * n) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hpt : ∀ R : SO n, frobSq (1 - (R : Matrix (Fin n) (Fin n) ℝ))
      = 2 * ((n : ℝ) - (R : Matrix (Fin n) (Fin n) ℝ).trace) := fun R => by
    rw [frobSq_one_sub (SO.coe_mem_orthogonal R), Fintype.card_fin]
  simp only [hpt]
  rw [integral_const_mul, one_sub_stdEig]
  field_simp

theorem continuous_frobSq_skewPart :
    Continuous fun R : SO n => frobSq (skewPart (R : Matrix (Fin n) (Fin n) ℝ)) := by
  simp only [frobSq, skewPart, Matrix.smul_apply, Matrix.sub_apply, transpose_apply, smul_eq_mul]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_const.mul ((continuous_entry i j).sub (continuous_entry j i))).pow 2

theorem integrable_frobSq_skewPart (ν : Measure (SO n)) [IsFiniteMeasure ν] :
    Integrable (fun R : SO n => frobSq (skewPart (R : Matrix (Fin n) (Fin n) ℝ))) ν :=
  continuous_frobSq_skewPart.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Lower bound:** `1 - λ ≥ E‖skew(R)‖² / (2n)`.  For the sampler, `skew(R)` is the tangent
step `A` on acceptance and `0` on rejection. -/
theorem one_sub_stdEig_ge (ν : Measure (SO n)) [IsProbabilityMeasure ν] [NeZero n] :
    (∫ R : SO n, frobSq (skewPart (R : Matrix (Fin n) (Fin n) ℝ)) ∂ν) / (2 * n)
      ≤ 1 - stdEig ν := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [one_sub_stdEig, div_le_div_iff₀ (by positivity) hn]
  have hint : Integrable
      (fun R : SO n => (n : ℝ) - (R : Matrix (Fin n) (Fin n) ℝ).trace) ν :=
    (integrable_const _).sub (integrable_trace ν)
  have hmono : ∫ R : SO n, frobSq (skewPart (R : Matrix (Fin n) (Fin n) ℝ)) ∂ν
      ≤ ∫ R : SO n, 2 * ((n : ℝ) - (R : Matrix (Fin n) (Fin n) ℝ).trace) ∂ν := by
    refine integral_mono (integrable_frobSq_skewPart ν) (hint.const_mul 2) fun R => ?_
    have := frobSq_skewPart_le (SO.coe_mem_orthogonal R)
    rwa [frobSq_one_sub (SO.coe_mem_orthogonal R), Fintype.card_fin] at this
  rw [integral_const_mul] at hmono
  nlinarith

/-! ### The tangent-space sampler -/

section Sampler

variable {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]

/-- `1 - λ` for the law of a random rotation `R`. -/
theorem one_sub_stdEig_map [NeZero n] {R : Ω → SO n} (hR : Measurable R) :
    1 - stdEig (ℙ.map R)
      = (∫ ω, ((n : ℝ) - (R ω : Matrix (Fin n) (Fin n) ℝ).trace) ∂ℙ) / n := by
  have : IsProbabilityMeasure (ℙ.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
  rw [one_sub_stdEig]
  congr 1
  have hc : Continuous fun R : SO n => (n : ℝ) - (R : Matrix (Fin n) (Fin n) ℝ).trace := by
    simp only [trace, diag_apply]
    exact continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_entry i i)
  exact integral_map hR.aemeasurable hc.aestronglyMeasurable

/-- **Upper bound for the sampler.** Let `R` be the random group step of a sampler whose
accepted moves are principal projections of a tangent proposal `A`: for every outcome, either
`R = 1` (rejection) or `R` has skew part `A` and positive semidefinite symmetric part.  Then
`1 - λ ≤ E‖A‖² / n`. -/
theorem one_sub_stdEig_le_of_step [NeZero n] {A : Ω → Matrix (Fin n) (Fin n) ℝ} {R : Ω → SO n}
    (hR : Measurable R)
    (hstep : ∀ ω, R ω = 1 ∨ (skewPart (R ω : Matrix (Fin n) (Fin n) ℝ) = A ω ∧
      (symPart (R ω : Matrix (Fin n) (Fin n) ℝ)).PosSemidef))
    (hA : Integrable (fun ω => frobSq (A ω)) ℙ) :
    1 - stdEig (ℙ.map R) ≤ (∫ ω, frobSq (A ω) ∂ℙ) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [one_sub_stdEig_map ℙ hR]
  refine div_le_div_of_nonneg_right ?_ hn.le
  have hc : Continuous fun R : SO n => (n : ℝ) - (R : Matrix (Fin n) (Fin n) ℝ).trace := by
    simp only [trace, diag_apply]
    exact continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_entry i i)
  have hint : Integrable (fun ω => (n : ℝ) - (R ω : Matrix (Fin n) (Fin n) ℝ).trace) ℙ := by
    refine Integrable.of_bound (hc.measurable.comp hR).aestronglyMeasurable (2 * n)
      (Filter.Eventually.of_forall fun ω => ?_)
    have htr : |(R ω : Matrix (Fin n) (Fin n) ℝ).trace| ≤ n := by
      simp only [trace, diag_apply]
      calc |∑ i, (R ω : Matrix (Fin n) (Fin n) ℝ) i i|
          ≤ ∑ i, |(R ω : Matrix (Fin n) (Fin n) ℝ) i i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => abs_entry_le_one _ i i
        _ = n := by simp
    rw [Real.norm_eq_abs]
    have := abs_le.mp htr
    rw [abs_le]
    constructor <;> linarith
  refine integral_mono hint hA fun ω => ?_
  rcases hstep ω with h1 | ⟨hskew, hpsd⟩
  · have : (R ω : Matrix (Fin n) (Fin n) ℝ) = 1 := by rw [h1]; rfl
    simp only [this, trace_one, Fintype.card_fin, sub_self]
    exact frobSq_nonneg _
  · have := (card_sub_trace_bounds (SO.coe_mem_orthogonal (R ω)) hpsd).2
    rwa [Fintype.card_fin, hskew] at this

omit [IsProbabilityMeasure ℙ] in
/-- Second moment of a skew-symmetric random matrix whose off-diagonal entries have second
moment `σ²`: `E‖A‖² = n (n - 1) σ²`. -/
theorem integral_frobSq_of_var {A : Ω → Matrix (Fin n) (Fin n) ℝ} {σ : ℝ}
    (hskew : ∀ ω, (A ω)ᵀ = -A ω) (hA : ∀ i j, Integrable (fun ω => A ω i j ^ 2) ℙ)
    (hvar : ∀ i j, i ≠ j → ∫ ω, A ω i j ^ 2 ∂ℙ = σ ^ 2) :
    ∫ ω, frobSq (A ω) ∂ℙ = n * (n - 1) * σ ^ 2 := by
  have hdiag : ∀ ω i, A ω i i = 0 := by
    intro ω i
    have := congrFun (congrFun (hskew ω) i) i
    simp only [transpose_apply, Matrix.neg_apply] at this
    linarith
  simp only [frobSq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hA i j)]
  have hrow : ∀ i : Fin n, ∫ ω, ∑ j, A ω i j ^ 2 ∂ℙ = (n - 1) * σ ^ 2 := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hA i j)]
    have : ∀ j : Fin n, ∫ ω, A ω i j ^ 2 ∂ℙ = if j = i then 0 else σ ^ 2 := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp [hdiag]
      · simp only [hji, ↓reduceIte]
        exact hvar i j (Ne.symm hji)
    simp only [this, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
      nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun j : Fin n => ¬ j = i).card = n - 1 := by
      rw [Finset.filter_ne' Finset.univ i, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
    rw [hcard]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      subst h0
      exact i.elim0)
    push_cast [Nat.cast_sub hn1]
    ring
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **Theorem (spectral gap of the tangent-space sampler on `SO(n)`).**  Let `n ≥ 2`.  Suppose
the group step `R` of the sampler is, for every outcome, either the identity (rejection) or the
principal projection of the tangent proposal `A` (skew part `A`, positive semidefinite symmetric
part); that `A` is skew-symmetric with off-diagonal second moments `σ²`; and that the law of `R`
is conjugation invariant.  Then every Poincaré constant of the sampler is at most `(n - 1) σ²`:
the spectral gap is at most `(n - 1) σ²`. -/
theorem sampler_gap_le (hn : 2 ≤ n) {A : Ω → Matrix (Fin n) (Fin n) ℝ} {R : Ω → SO n}
    (hR : Measurable R)
    (hstep : ∀ ω, R ω = 1 ∨ (skewPart (R ω : Matrix (Fin n) (Fin n) ℝ) = A ω ∧
      (symPart (R ω : Matrix (Fin n) (Fin n) ℝ)).PosSemidef))
    {σ : ℝ} (hskew : ∀ ω, (A ω)ᵀ = -A ω) (hA : ∀ i j, Integrable (fun ω => A ω i j ^ 2) ℙ)
    (hvar : ∀ i j, i ≠ j → ∫ ω, A ω i j ^ 2 ∂ℙ = σ ^ 2)
    (hν : ConjInvariant (ℙ.map R)) {γ : ℝ} (hγ : PoincareIneq (haarSO n) (ℙ.map R) γ) :
    γ ≤ (n - 1) * σ ^ 2 := by
  have : NeZero n := ⟨by omega⟩
  have : IsProbabilityMeasure (ℙ.map R) := Measure.isProbabilityMeasure_map hR.aemeasurable
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hAint : Integrable (fun ω => frobSq (A ω)) ℙ := by
    simp only [frobSq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hA i j
  have h1 := gap_le_of_conjInvariant hn (ℙ.map R) hν hγ
  have h2 := one_sub_stdEig_le_of_step ℙ hR hstep hAint
  rw [integral_frobSq_of_var ℙ hskew hA hvar] at h2
  have h3 : (n : ℝ) * (n - 1) * σ ^ 2 / n = (n - 1) * σ ^ 2 := by
    field_simp
  linarith

end Sampler

end SOnMCMC

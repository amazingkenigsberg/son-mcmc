import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import SOnMCMC.SOn

/-!
# The group `SU(2)`

Paper: Section 6.1.

`SU(2)` is the double cover of `SO(3)`, and its harmonic analysis is explicit.  This file sets
up the group: it is a compact topological group with a bi-invariant Haar probability measure
`haarSU2`; its elements are the matrices `!![a, b; -conj b, conj a]` with `|a|² + |b|² = 1`
(`SU2.coe_11`, `SU2.coe_10`, `SU2.mk'`); and `lin u v x = uᵀ x v` are the linear forms in the
matrix entries from which the eigenfunctions are built.
-/

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace SOnMCMC

/-- The special unitary group `SU(2)`. -/
abbrev SU2 : Type := specialUnitaryGroup (Fin 2) ℂ

namespace SU2

theorem coe_mem_unitary (x : SU2) :
    (x : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitaryGroup (Fin 2) ℂ :=
  (mem_specialUnitaryGroup_iff.mp x.2).1

theorem det_coe (x : SU2) : (x : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
  (mem_specialUnitaryGroup_iff.mp x.2).2

instance instSecondCountableTopology : SecondCountableTopology SU2 := by
  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology _

/-- `SU(2)` is a topological group. -/
instance instIsTopologicalGroup : IsTopologicalGroup SU2 where
  continuous_inv := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_subtype_val.matrix_conjTranspose

/-- `SU(2)` is compact. -/
instance instCompactSpace : CompactSpace SU2 := by
  have hK : IsCompact {A : Matrix (Fin 2) (Fin 2) ℂ |
      ∀ i j, A i j ∈ Metric.closedBall (0 : ℂ) 1} := by
    have : {A : Matrix (Fin 2) (Fin 2) ℂ | ∀ i j, A i j ∈ Metric.closedBall (0 : ℂ) 1}
        = Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ
            (fun _ : Fin 2 => Metric.closedBall (0 : ℂ) 1)) := by
      ext A
      constructor
      · intro h i _ j _
        exact h i j
      · intro h i j
        exact h i (Set.mem_univ _) j (Set.mem_univ _)
    rw [this]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hclosed : IsClosed (specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    have : (specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))
        = {A | A * Aᴴ = 1} ∩ {A | A.det = 1} := by
      ext A
      simp [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose]
    rw [this]
    exact (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
      continuous_const).inter (isClosed_eq continuous_id.matrix_det continuous_const)
  have hsub : (specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))
      ⊆ {A | ∀ i j, A i j ∈ Metric.closedBall (0 : ℂ) 1} := by
    intro A hA i j
    have hU : A ∈ unitaryGroup (Fin 2) ℂ := (mem_specialUnitaryGroup_iff.mp hA).1
    simpa using entry_norm_bound_of_unitary hU i j
  exact isCompact_iff_compactSpace.mp (hK.of_isClosed_subset hclosed hsub)

/-! ### The entries of an element of `SU(2)` -/

theorem star_eq_adjugate (x : SU2) :
    star (x : Matrix (Fin 2) (Fin 2) ℂ) = adjugate (x : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : star (x : Matrix (Fin 2) (Fin 2) ℂ) * (x : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    mem_unitaryGroup_iff'.mp (coe_mem_unitary x)
  have h2 : (x : Matrix (Fin 2) (Fin 2) ℂ) * adjugate (x : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [mul_adjugate, det_coe, one_smul]
  calc star (x : Matrix (Fin 2) (Fin 2) ℂ)
      = star (x : Matrix (Fin 2) (Fin 2) ℂ)
          * ((x : Matrix (Fin 2) (Fin 2) ℂ) * adjugate (x : Matrix (Fin 2) (Fin 2) ℂ)) := by
        rw [h2, Matrix.mul_one]
    _ = adjugate (x : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- The lower right entry is the conjugate of the upper left one. -/
theorem coe_11 (x : SU2) :
    (x : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = conj ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  have h := congrFun (congrFun (star_eq_adjugate x) 0) 0
  rw [adjugate_fin_two] at h
  simpa [star_apply] using h.symm

/-- The lower left entry is minus the conjugate of the upper right one. -/
theorem coe_10 (x : SU2) :
    (x : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -conj ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  have h := congrFun (congrFun (star_eq_adjugate x) 1) 0
  rw [adjugate_fin_two] at h
  have h' : conj ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = -(x : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    simpa [star_apply] using h
  rw [h', neg_neg]

theorem det_eq (x : SU2) :
    (x : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (x : Matrix (Fin 2) (Fin 2) ℂ) 1 1
      - (x : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (x : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
  rw [← det_fin_two, det_coe]

theorem normSq_add (x : SU2) :
    (x : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * conj ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
      + (x : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * conj ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 1 := by
  have h := det_eq x
  rw [coe_11, coe_10] at h
  linear_combination h

/-- The element `!![a, b; -conj b, conj a]` of `SU(2)`, for `|a|² + |b|² = 1`. -/
def mk' (a b : ℂ) (h : a * conj a + b * conj b = 1) : SU2 :=
  ⟨!![a, b; -conj b, conj a], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
    constructor
    · rw [star_eq_conjTranspose]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
          | linear_combination h
          | ring
    · rw [det_fin_two_of]
      linear_combination h⟩

@[simp] theorem mk'_coe (a b : ℂ) (h : a * conj a + b * conj b = 1) :
    ((mk' a b h : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; -conj b, conj a] := rfl

/-- Every element of `SU(2)` is of the form `mk' a b`. -/
theorem coe_eq (x : SU2) :
    (x : Matrix (Fin 2) (Fin 2) ℂ)
      = !![(x : Matrix (Fin 2) (Fin 2) ℂ) 0 0, (x : Matrix (Fin 2) (Fin 2) ℂ) 0 1;
          -conj ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 1), conj ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_10, coe_11]

end SU2

/-! ### Haar measure -/

/-- Normalised Haar measure on `SU(2)`. -/
noncomputable def haarSU2 : Measure SU2 := Measure.haarMeasure ⊤

instance haarSU2.instIsHaarMeasure : haarSU2.IsHaarMeasure := by
  unfold haarSU2
  infer_instance

instance haarSU2.instIsProbabilityMeasure : IsProbabilityMeasure haarSU2 :=
  ⟨Measure.haarMeasure_self⟩

instance haarSU2.instIsMulRightInvariant : haarSU2.IsMulRightInvariant :=
  isMulRightInvariant_of_compact _

/-! ### Linear forms in the entries -/

/-- The linear form `x ↦ uᵀ x v` in the entries of `x ∈ SU(2)`. -/
def lin (u v : Fin 2 → ℂ) (x : SU2) : ℂ := u ⬝ᵥ ((x : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)

theorem lin_apply (u v : Fin 2 → ℂ) (x : SU2) :
    lin u v x = u 0 * ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * v 0
        + (x : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * v 1)
      + u 1 * ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * v 0
        + (x : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * v 1) := by
  simp [lin, dotProduct, mulVec, Fin.sum_univ_two]

theorem lin_mul (u v : Fin 2 → ℂ) (x q : SU2) :
    lin u v (x * q) = lin (u ᵥ* (x : Matrix (Fin 2) (Fin 2) ℂ)) v q := by
  show u ⬝ᵥ (((x : Matrix (Fin 2) (Fin 2) ℂ) * (q : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ v) = _
  rw [lin, ← mulVec_mulVec, dotProduct_mulVec]

theorem lin_add_left (u u' v : Fin 2 → ℂ) : lin (u + u') v = lin u v + lin u' v := by
  funext x
  simp [lin, add_dotProduct]

theorem lin_smul_left (c : ℂ) (u v : Fin 2 → ℂ) : lin (c • u) v = c • lin u v := by
  funext x
  simp [lin, smul_dotProduct]

theorem lin_add_right (u v v' : Fin 2 → ℂ) : lin u (v + v') = lin u v + lin u v' := by
  funext x
  simp [lin, mulVec_add, dotProduct_add]

theorem lin_smul_right (c : ℂ) (u v : Fin 2 → ℂ) : lin u (c • v) = c • lin u v := by
  funext x
  simp [lin, mulVec_smul, dotProduct_smul]

theorem continuous_lin (u v : Fin 2 → ℂ) : Continuous (lin u v) := by
  have h : ∀ i j, Continuous fun x : SU2 => (x : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j =>
    continuous_subtype_val.matrix_elem i j
  have : lin u v = fun x : SU2 => u 0 * ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * v 0
        + (x : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * v 1)
      + u 1 * ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * v 0
        + (x : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * v 1) := funext (lin_apply u v)
  rw [this]
  exact (continuous_const.mul (((h 0 0).mul continuous_const).add
      ((h 0 1).mul continuous_const))).add
    (continuous_const.mul (((h 1 0).mul continuous_const).add ((h 1 1).mul continuous_const)))

/-- The coordinate functions are linear forms. -/
theorem lin_single (i j : Fin 2) (x : SU2) :
    lin (Pi.single i 1) (Pi.single j 1) x = (x : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  simp [lin]

end SOnMCMC

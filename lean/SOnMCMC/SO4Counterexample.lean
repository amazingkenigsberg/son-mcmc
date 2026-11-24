import SOnMCMC.SecondEigenvalue

/-!
# `SO(4)`: the standard representation need not give the spectral gap

Paper: Section 7.

On `SO(3)` the spectral gap of every conjugation-invariant walk whose steps have positive
semidefinite symmetric part is `1 - E[tr R]/3` (`SO3Gap.lean`).  This file shows that the same
statement is false on `SO(4)`.

Let `J` be the rotation by `π/2` in the two coordinate planes `{0,1}` and `{2,3}`, and let
`so4Step` be the uniform distribution on the `O(4)`-conjugacy class of `J`.  Then

* `so4Step_conjInvariant`: the step distribution is conjugation invariant;
* `ae_posSemidef_so4Step`: every step has symmetric part `0`, which is positive semidefinite;
* `stdEig_so4Step`: `E[tr R]/4 = 0`, so the standard representation predicts a gap of `1`;
* `minorEig_so4Step`: the eigenvalue on two-by-two minors is `1/3`;
* `so4_poincare_le`: so every Poincaré constant is at most `2/3`;
* `so4_counterexample`: the Poincaré inequality with constant `1 - E[tr R]/4` fails.
-/

open MeasureTheory Matrix

namespace SOnMCMC

variable {n : ℕ}

/-! ### Haar measure on `O(n)` -/

/-- The orthogonal group `O(n)`. -/
abbrev On (n : ℕ) : Type := orthogonalGroup (Fin n) ℝ

instance On.instSecondCountableTopology : SecondCountableTopology (On n) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  exact TopologicalSpace.Subtype.secondCountableTopology _

instance On.instIsTopologicalGroup : IsTopologicalGroup (On n) where
  continuous_inv := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_subtype_val.matrix_transpose

instance On.instCompactSpace : CompactSpace (On n) := by
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
  have hclosed : IsClosed (orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
    have : (orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) = {A | A * Aᵀ = 1} := by
      ext A
      simp [mem_orthogonalGroup_iff]
    rw [this]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_transpose) continuous_const
  have hsub : (orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ))
      ⊆ {A | ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1} := by
    intro A hA i j
    have := entry_norm_bound_of_unitary hA i j
    rwa [Real.norm_eq_abs, abs_le] at this
  exact isCompact_iff_compactSpace.mp (hK.of_isClosed_subset hclosed hsub)

/-- Normalised Haar measure on `O(n)`. -/
noncomputable def haarO (n : ℕ) : Measure (On n) := Measure.haarMeasure ⊤

instance haarO.instIsHaarMeasure : (haarO n).IsHaarMeasure := by
  unfold haarO
  infer_instance

instance haarO.instIsProbabilityMeasure : IsProbabilityMeasure (haarO n) :=
  ⟨Measure.haarMeasure_self⟩

/-! ### Orbit measures -/

theorem continuous_conjO_left (R₀ : SO n) : Continuous fun Q : On n => conjO Q R₀ :=
  Continuous.subtype_mk ((continuous_subtype_val.matrix_mul continuous_const).matrix_mul
    continuous_subtype_val.matrix_transpose) _

theorem conjO_mul (Q' Q : On n) (R : SO n) : conjO (Q' * Q) R = conjO Q' (conjO Q R) := by
  apply Subtype.ext
  show ((Q' : Matrix (Fin n) (Fin n) ℝ) * (Q : Matrix (Fin n) (Fin n) ℝ))
      * (R : Matrix (Fin n) (Fin n) ℝ)
      * ((Q' : Matrix (Fin n) (Fin n) ℝ) * (Q : Matrix (Fin n) (Fin n) ℝ))ᵀ
    = (Q' : Matrix (Fin n) (Fin n) ℝ) * ((Q : Matrix (Fin n) (Fin n) ℝ)
      * (R : Matrix (Fin n) (Fin n) ℝ) * (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ)
      * (Q' : Matrix (Fin n) (Fin n) ℝ)ᵀ
  rw [transpose_mul]
  simp only [Matrix.mul_assoc]

/-- The uniform distribution on the `O(n)`-conjugacy class of `R₀`. -/
noncomputable def orbitMeasure (R₀ : SO n) : Measure (SO n) :=
  (haarO n).map (fun Q => conjO Q R₀)

instance (R₀ : SO n) : IsProbabilityMeasure (orbitMeasure R₀) :=
  Measure.isProbabilityMeasure_map (continuous_conjO_left R₀).measurable.aemeasurable

/-- **An orbit measure is conjugation invariant.** -/
theorem orbitMeasure_conjInvariant (R₀ : SO n) : ConjInvariant (orbitMeasure R₀) := by
  intro Q'
  have hc := (continuous_conjO_left R₀).measurable
  have hcomp : conjO Q' ∘ (fun Q : On n => conjO Q R₀)
      = (fun Q : On n => conjO Q R₀) ∘ fun Q => Q' * Q := by
    funext Q
    simp [conjO_mul]
  rw [orbitMeasure, Measure.map_map (continuous_conjO Q').measurable hc, hcomp,
    ← Measure.map_map hc (measurable_const_mul Q'), map_mul_left_eq_self]

theorem integral_orbitMeasure (R₀ : SO n) {F : SO n → ℝ} (hF : Continuous F) :
    ∫ R, F R ∂(orbitMeasure R₀) = ∫ Q, F (conjO Q R₀) ∂(haarO n) :=
  integral_map (continuous_conjO_left R₀).measurable.aemeasurable hF.aestronglyMeasurable

theorem trace_orth_conj (Q : On n) (M : Matrix (Fin n) (Fin n) ℝ) :
    ((Q : Matrix (Fin n) (Fin n) ℝ) * M * (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ).trace = M.trace := by
  have hQ : (Q : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Q : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (mem_orthogonalGroup_iff' (Fin n) ℝ).mp Q.2
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ, Matrix.one_mul]

/-! ### The step distribution -/

/-- Rotation by `π/2` in the coordinate planes `{0,1}` and `{2,3}`. -/
def J4mat : Matrix (Fin 4) (Fin 4) ℝ := !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

theorem J4mat_orth : J4mat ∈ orthogonalGroup (Fin 4) ℝ := by
  rw [mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J4mat, Matrix.mul_apply, Fin.sum_univ_four]

theorem symPart_J4mat : symPart J4mat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symPart, J4mat]

theorem trace_J4mat : J4mat.trace = 0 := by
  simp [J4mat, Matrix.trace, Fin.sum_univ_four]

theorem trace_J4mat_sq : (J4mat * J4mat).trace = -4 := by
  simp [J4mat, Matrix.trace, Fin.sum_univ_four]
  norm_num

/-- `J` as an element of `SO(4)`. -/
def J4 : SO 4 :=
  ⟨J4mat, mem_specialOrthogonalGroup_iff.mpr ⟨J4mat_orth,
    det_eq_one_of_posSemidef J4mat_orth (by
      rw [symPart_J4mat]
      exact PosSemidef.zero)⟩⟩

/-- **The step distribution:** uniform on the `O(4)`-conjugacy class of `J`. -/
noncomputable def so4Step : Measure (SO 4) := orbitMeasure J4

instance : IsProbabilityMeasure so4Step := by
  unfold so4Step
  infer_instance

theorem so4Step_conjInvariant : ConjInvariant so4Step := orbitMeasure_conjInvariant J4

/-- Every step has symmetric part `0`. -/
theorem ae_posSemidef_so4Step :
    ∀ᵐ R : SO 4 ∂so4Step, (symPart (R : Matrix (Fin 4) (Fin 4) ℝ)).PosSemidef := by
  have hcont : Continuous fun R : SO 4 => symPart (R : Matrix (Fin 4) (Fin 4) ℝ) := by
    have h1 : Continuous fun R : SO 4 => (R : Matrix (Fin 4) (Fin 4) ℝ) :=
      continuous_subtype_val
    have h2 : Continuous fun R : SO 4 =>
        (R : Matrix (Fin 4) (Fin 4) ℝ) + (R : Matrix (Fin 4) (Fin 4) ℝ)ᵀ :=
      h1.add h1.matrix_transpose
    exact h2.const_smul (1 / 2 : ℝ)
  have hclosed : IsClosed {R : SO 4 | (symPart (R : Matrix (Fin 4) (Fin 4) ℝ)).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage hcont
  rw [so4Step, orbitMeasure,
    ae_map_iff (continuous_conjO_left J4).measurable.aemeasurable hclosed.measurableSet]
  refine Filter.Eventually.of_forall fun Q => ?_
  show (symPart ((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ)).PosSemidef
  refine posSemidef_symPart_conj _ ?_
  rw [symPart_J4mat]
  exact PosSemidef.zero

/-- The standard representation has eigenvalue `E[tr R]/4 = 0`. -/
theorem stdEig_so4Step : stdEig so4Step = 0 := by
  have htr : Continuous fun R : SO 4 => (R : Matrix (Fin 4) (Fin 4) ℝ).trace :=
    continuous_subtype_val.matrix_trace
  rw [stdEig, so4Step, integral_orbitMeasure J4 htr]
  have h0 : ∀ Q : On 4, ((conjO Q J4 : SO 4) : Matrix (Fin 4) (Fin 4) ℝ).trace = 0 := by
    intro Q
    show ((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ).trace = 0
    rw [trace_orth_conj, trace_J4mat]
  simp only [h0, integral_zero, zero_div]

/-- The sum of the six principal `2 × 2` minors. -/
def e2 (R : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  minor2 0 1 0 1 R + minor2 0 2 0 2 R + minor2 0 3 0 3 R + minor2 1 2 1 2 R + minor2 1 3 1 3 R
    + minor2 2 3 2 3 R

theorem e2_eq (R : Matrix (Fin 4) (Fin 4) ℝ) : e2 R = (R.trace ^ 2 - (R * R).trace) / 2 := by
  simp [e2, minor2, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem e2_conj_J4 (Q : On 4) : e2 ((conjO Q J4 : SO 4) : Matrix (Fin 4) (Fin 4) ℝ) = 2 := by
  have hQ : (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * (Q : Matrix (Fin 4) (Fin 4) ℝ) = 1 :=
    (mem_orthogonalGroup_iff' (Fin 4) ℝ).mp Q.2
  have hsq : ((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ)
      * ((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ)
      = (Q : Matrix (Fin 4) (Fin 4) ℝ) * (J4mat * J4mat) * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ := by
    calc ((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ)
          * ((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ)
        = (Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat
          * ((Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * (Q : Matrix (Fin 4) (Fin 4) ℝ))
          * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (Q : Matrix (Fin 4) (Fin 4) ℝ) * (J4mat * J4mat) * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ := by
          rw [hQ, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [e2_eq]
  show (((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ).trace ^ 2
    - (((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ)
      * ((Q : Matrix (Fin 4) (Fin 4) ℝ) * J4mat * (Q : Matrix (Fin 4) (Fin 4) ℝ)ᵀ)).trace) / 2 = 2
  rw [hsq, trace_orth_conj, trace_orth_conj, trace_J4mat, trace_J4mat_sq]
  norm_num

/-- **The eigenvalue on two-by-two minors is `1/3`.** -/
theorem minorEig_so4Step : minorEig so4Step 0 1 = 1 / 3 := by
  have hν := so4Step_conjInvariant
  -- all six pairs give the same eigenvalue
  have h02 : minorEig so4Step 0 2 = minorEig so4Step 0 1 := by
    have h := minorEig_swap so4Step hν 1 2 0 1
    have e1 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
    have e2 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
    rwa [e1, e2] at h
  have h03 : minorEig so4Step 0 3 = minorEig so4Step 0 1 := by
    have h := minorEig_swap so4Step hν 1 3 0 1
    have e1 : Equiv.swap (1 : Fin 4) 3 0 = 0 := by decide
    have e2 : Equiv.swap (1 : Fin 4) 3 1 = 3 := by decide
    rwa [e1, e2] at h
  have h12 : minorEig so4Step 1 2 = minorEig so4Step 0 1 := by
    have h := minorEig_swap so4Step hν 0 2 0 1
    have e1 : Equiv.swap (0 : Fin 4) 2 0 = 2 := by decide
    have e2 : Equiv.swap (0 : Fin 4) 2 1 = 1 := by decide
    rw [e1, e2, minorEig_comm] at h
    exact h
  have h13 : minorEig so4Step 1 3 = minorEig so4Step 0 1 := by
    have h := minorEig_swap so4Step hν 0 3 0 1
    have e1 : Equiv.swap (0 : Fin 4) 3 0 = 3 := by decide
    have e2 : Equiv.swap (0 : Fin 4) 3 1 = 1 := by decide
    rw [e1, e2, minorEig_comm] at h
    exact h
  have h23 : minorEig so4Step 2 3 = minorEig so4Step 0 1 := by
    have h := minorEig_swap so4Step hν 0 3 0 2
    have e1 : Equiv.swap (0 : Fin 4) 3 0 = 3 := by decide
    have e2 : Equiv.swap (0 : Fin 4) 3 2 = 2 := by decide
    rw [e1, e2, minorEig_comm, h02] at h
    exact h
  -- the sum of the six eigenvalues is `E[e₂(R)] = 2`
  have hcont : Continuous fun R : SO 4 => e2 (R : Matrix (Fin 4) (Fin 4) ℝ) := by
    unfold e2
    exact ((((continuous_minor2 0 1 0 1).add (continuous_minor2 0 2 0 2)).add
      (continuous_minor2 0 3 0 3)).add (continuous_minor2 1 2 1 2)).add
        (continuous_minor2 1 3 1 3) |>.add (continuous_minor2 2 3 2 3)
  have hsum : ∫ R : SO 4, e2 (R : Matrix (Fin 4) (Fin 4) ℝ) ∂so4Step = 2 := by
    rw [so4Step, integral_orbitMeasure J4 hcont]
    simp only [e2_conj_J4, integral_const, probReal_univ, one_smul]
  have hsplit : ∫ R : SO 4, e2 (R : Matrix (Fin 4) (Fin 4) ℝ) ∂so4Step
      = minorEig so4Step 0 1 + minorEig so4Step 0 2 + minorEig so4Step 0 3
        + minorEig so4Step 1 2 + minorEig so4Step 1 3 + minorEig so4Step 2 3 := by
    have i01 := integrable_minor2 so4Step 0 1 0 1
    have i02 := integrable_minor2 so4Step 0 2 0 2
    have i03 := integrable_minor2 so4Step 0 3 0 3
    have i12 := integrable_minor2 so4Step 1 2 1 2
    have i13 := integrable_minor2 so4Step 1 3 1 3
    have i23 := integrable_minor2 so4Step 2 3 2 3
    have a1 : Integrable (fun R : SO 4 => minor2 0 1 0 1 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 0 2 0 2 (R : Matrix (Fin 4) (Fin 4) ℝ)) so4Step := i01.add i02
    have a2 : Integrable (fun R : SO 4 => minor2 0 1 0 1 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 0 2 0 2 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 0 3 0 3 (R : Matrix (Fin 4) (Fin 4) ℝ)) so4Step := a1.add i03
    have a3 : Integrable (fun R : SO 4 => minor2 0 1 0 1 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 0 2 0 2 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 0 3 0 3 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 1 2 1 2 (R : Matrix (Fin 4) (Fin 4) ℝ)) so4Step := a2.add i12
    have a4 : Integrable (fun R : SO 4 => minor2 0 1 0 1 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 0 2 0 2 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 0 3 0 3 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 1 2 1 2 (R : Matrix (Fin 4) (Fin 4) ℝ)
        + minor2 1 3 1 3 (R : Matrix (Fin 4) (Fin 4) ℝ)) so4Step := a3.add i13
    simp only [e2, minorEig]
    rw [integral_add a4 i23, integral_add a3 i13, integral_add a2 i12, integral_add a1 i03,
      integral_add i01 i02]
  rw [hsplit, h02, h03, h12, h13, h23] at hsum
  linarith

/-- **Theorem.** Every Poincaré constant of the walk on `SO(4)` with step distribution
`so4Step` is at most `2/3`. -/
theorem so4_poincare_le {γ : ℝ} (hγ : PoincareIneq (haarSO 4) so4Step γ) : γ ≤ 2 / 3 := by
  have h := gap_le_one_sub_minorEig (by norm_num) so4Step so4Step_conjInvariant
    (i := 0) (j := 1) (by decide) hγ
  rw [minorEig_so4Step] at h
  linarith

/-- **Theorem (the `SO(3)` result fails on `SO(4)`).** There is a conjugation-invariant step
distribution on `SO(4)` all of whose steps have positive semidefinite symmetric part, for which
the Poincaré inequality with constant `1 - E[tr R]/4` is false: the spectral gap is strictly
smaller than the bound given by the standard representation. -/
theorem so4_counterexample :
    ∃ ν : Measure (SO 4), IsProbabilityMeasure ν ∧ ConjInvariant ν ∧
      (∀ᵐ R : SO 4 ∂ν, (symPart (R : Matrix (Fin 4) (Fin 4) ℝ)).PosSemidef) ∧
      ¬ PoincareIneq (haarSO 4) ν (1 - stdEig ν) := by
  refine ⟨so4Step, inferInstance, so4Step_conjInvariant, ae_posSemidef_so4Step, fun h => ?_⟩
  have h1 := so4_poincare_le h
  rw [stdEig_so4Step] at h1
  norm_num at h1

end SOnMCMC

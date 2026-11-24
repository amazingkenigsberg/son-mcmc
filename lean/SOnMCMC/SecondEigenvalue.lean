import SOnMCMC.SOn

/-!
# A second eigenvalue: the walk on two-by-two minors

Paper: Section 7.

For a conjugation-invariant step distribution `ν` on `SO(n)`, the `2 × 2` minors of `X`
(matrix coefficients of the second exterior power of the standard representation) are
eigenfunctions of the walk:

* `markovOp_minor2`: `P m = λ₂ m` for `m(X) = X_{ai} X_{bj} - X_{aj} X_{bi}`, with
  `λ₂ = minorEig ν i j = E[R_{ii} R_{jj} - R_{ij} R_{ji}]`;
* `gap_le_one_sub_minorEig`: hence, for `n ≥ 3`, every Poincaré constant is at most `1 - λ₂`;
* `minorEig_eq`: `λ₂` does not depend on the pair `i ≠ j`.

Together with `gap_le_of_conjInvariant` this gives `gap ≤ 1 - max (λ₁, λ₂)`.  For `n = 3` the
maximum is always `λ₁` when the steps have positive semidefinite symmetric part
(`SO3Gap.lean`); for `n = 4` it can be `λ₂` (`SO4Counterexample.lean`).
-/

open MeasureTheory Matrix

namespace SOnMCMC

variable {n : ℕ}

/-- The `2 × 2` minor of `X` with rows `a, b` and columns `i, j`. -/
def minor2 (a b i j : Fin n) (X : Matrix (Fin n) (Fin n) ℝ) : ℝ := X a i * X b j - X a j * X b i

theorem continuous_minor2 (a b i j : Fin n) :
    Continuous fun X : SO n => minor2 a b i j (X : Matrix (Fin n) (Fin n) ℝ) :=
  ((continuous_entry a i).mul (continuous_entry b j)).sub
    ((continuous_entry a j).mul (continuous_entry b i))

theorem integrable_minor2 (ν : Measure (SO n)) [IsFiniteMeasure ν] (a b i j : Fin n) :
    Integrable (fun X : SO n => minor2 a b i j (X : Matrix (Fin n) (Fin n) ℝ)) ν :=
  (continuous_minor2 a b i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **The eigenvalue of the walk on the second exterior power:**
`λ₂(ν) = E[R_{ii} R_{jj} - R_{ij} R_{ji}]`. -/
noncomputable def minorEig (ν : Measure (SO n)) (i j : Fin n) : ℝ :=
  ∫ R : SO n, minor2 i j i j (R : Matrix (Fin n) (Fin n) ℝ) ∂ν

/-- Integrals against a conjugation-invariant measure are invariant under conjugation. -/
theorem integral_conjO (ν : Measure (SO n)) (hν : ConjInvariant ν)
    (Q : orthogonalGroup (Fin n) ℝ) {F : SO n → ℝ} (hF : Continuous F) :
    ∫ R, F (conjO Q R) ∂ν = ∫ R, F R ∂ν := by
  have h := integral_map (μ := ν) (continuous_conjO Q).measurable.aemeasurable (f := F)
    hF.aestronglyMeasurable
  rw [hν Q] at h
  exact h.symm

/-- The sign of the reflection `flipMat c` in coordinate `a`. -/
def flipSign (c a : Fin n) : ℝ := if a = c then -1 else 1

theorem minor2_conj_flip (c k l i j : Fin n) (R : SO n) :
    minor2 k l i j (conjO ⟨flipMat c, flipMat_mem c⟩ R : Matrix (Fin n) (Fin n) ℝ)
      = flipSign c k * flipSign c l * flipSign c i * flipSign c j
        * minor2 k l i j (R : Matrix (Fin n) (Fin n) ℝ) := by
  simp only [coe_conjO, minor2, flipMat, flipSign, diagonal_transpose, mul_diagonal,
    diagonal_mul]
  ring

theorem integral_minor2_eq_zero (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    {c k l i j : Fin n}
    (hs : flipSign c k * flipSign c l * flipSign c i * flipSign c j = -1) :
    ∫ R : SO n, minor2 k l i j (R : Matrix (Fin n) (Fin n) ℝ) ∂ν = 0 := by
  have h := integral_conjO ν hν ⟨flipMat c, flipMat_mem c⟩ (continuous_minor2 k l i j)
  simp only [minor2_conj_flip, hs] at h
  rw [integral_const_mul] at h
  linarith

/-- **Schur's lemma for the second exterior power, by hand.** -/
theorem integral_minor2 (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    {i j : Fin n} (hij : i ≠ j) (k l : Fin n) :
    ∫ R : SO n, minor2 k l i j (R : Matrix (Fin n) (Fin n) ℝ) ∂ν
      = minorEig ν i j * ((if k = i then 1 else 0) * (if l = j then 1 else 0)
          - (if k = j then 1 else 0) * (if l = i then 1 else 0)) := by
  by_cases hkl : k = l
  · rw [hkl]
    have h0 : ∀ R : SO n, minor2 l l i j (R : Matrix (Fin n) (Fin n) ℝ) = 0 := fun R => by
      simp only [minor2]
      ring
    simp only [h0, integral_zero]
    ring
  · by_cases hki : k = i
    · by_cases hlj : l = j
      · rw [hki, hlj]
        simp [minorEig, hij]
      · have hli : l ≠ i := fun h => hkl (hki.trans h.symm)
        rw [integral_minor2_eq_zero ν hν (c := l)
          (by simp [flipSign, hkl, Ne.symm hli, Ne.symm hlj])]
        simp [hlj, hli]
    · by_cases hkj : k = j
      · by_cases hli : l = i
        · rw [hkj, hli]
          have h1 : ∀ R : SO n, minor2 j i i j (R : Matrix (Fin n) (Fin n) ℝ)
              = -minor2 i j i j (R : Matrix (Fin n) (Fin n) ℝ) := fun R => by
            simp only [minor2]
            ring
          simp only [h1, integral_neg]
          simp [minorEig, hij, Ne.symm hij]
        · have hlj : l ≠ j := fun h => hkl (hkj.trans h.symm)
          rw [integral_minor2_eq_zero ν hν (c := l)
            (by simp [flipSign, hkl, Ne.symm hli, Ne.symm hlj])]
          simp [hlj, hli]
      · rw [integral_minor2_eq_zero ν hν (c := k)
          (by simp [flipSign, Ne.symm hkl, Ne.symm hki, Ne.symm hkj])]
        simp [hki, hkj]

theorem sum_sum_delta (c d : Fin n → ℝ) (lam : ℝ) (i j : Fin n) :
    ∑ k, ∑ l, c k * d l * (lam * ((if k = i then 1 else 0) * (if l = j then 1 else 0)
        - (if k = j then 1 else 0) * (if l = i then 1 else 0)))
      = lam * (c i * d j - c j * d i) := by
  have e1 : ∀ (f : Fin n → ℝ) (i : Fin n), ∑ k, f k * (if k = i then (1 : ℝ) else 0) = f i := by
    intro f i
    simp
  have h1 : ∀ k l, c k * d l * (lam * ((if k = i then 1 else 0) * (if l = j then 1 else 0)
        - (if k = j then 1 else 0) * (if l = i then 1 else 0)))
      = lam * ((c k * (if k = i then 1 else 0)) * (d l * (if l = j then 1 else 0))
        - (c k * (if k = j then 1 else 0)) * (d l * (if l = i then 1 else 0))) := by
    intro k l
    ring
  simp only [h1]
  rw [← e1 c i, ← e1 d j, ← e1 c j, ← e1 d i, Finset.sum_mul_sum, Finset.sum_mul_sum,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]

/-- **Two-by-two minors are eigenfunctions.** For a conjugation-invariant step distribution,
the minor of `X` with rows `a, b` and columns `i ≠ j` satisfies `P m = λ₂ m`. -/
theorem markovOp_minor2 (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    {i j : Fin n} (hij : i ≠ j) (a b : Fin n) :
    markovOp ν (fun X : SO n => minor2 a b i j (X : Matrix (Fin n) (Fin n) ℝ))
      = fun X : SO n => minorEig ν i j * minor2 a b i j (X : Matrix (Fin n) (Fin n) ℝ) := by
  funext X
  have hexp : ∀ R : SO n, minor2 a b i j ((X * R : SO n) : Matrix (Fin n) (Fin n) ℝ)
      = ∑ k, ∑ l, (X : Matrix (Fin n) (Fin n) ℝ) a k * (X : Matrix (Fin n) (Fin n) ℝ) b l
          * minor2 k l i j (R : Matrix (Fin n) (Fin n) ℝ) := by
    intro R
    show minor2 a b i j ((X : Matrix (Fin n) (Fin n) ℝ) * (R : Matrix (Fin n) (Fin n) ℝ)) = _
    simp only [minor2, Matrix.mul_apply]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hint : ∀ k l : Fin n, Integrable (fun R : SO n =>
      (X : Matrix (Fin n) (Fin n) ℝ) a k * (X : Matrix (Fin n) (Fin n) ℝ) b l
        * minor2 k l i j (R : Matrix (Fin n) (Fin n) ℝ)) ν :=
    fun k l => (integrable_minor2 ν k l i j).const_mul _
  simp only [markovOp, hexp]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  have h2 : ∀ k : Fin n, ∫ R : SO n, ∑ l, (X : Matrix (Fin n) (Fin n) ℝ) a k
        * (X : Matrix (Fin n) (Fin n) ℝ) b l * minor2 k l i j (R : Matrix (Fin n) (Fin n) ℝ) ∂ν
      = ∑ l, (X : Matrix (Fin n) (Fin n) ℝ) a k * (X : Matrix (Fin n) (Fin n) ℝ) b l
        * (minorEig ν i j * ((if k = i then 1 else 0) * (if l = j then 1 else 0)
          - (if k = j then 1 else 0) * (if l = i then 1 else 0))) := by
    intro k
    rw [integral_finsetSum _ fun l _ => hint k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_minor2 ν hν hij]
  simp only [h2]
  rw [sum_sum_delta]
  simp only [minor2]

/-! ### Haar mean and norm of the minors -/

theorem exists_ne_ne (hn : 3 ≤ n) (i j : Fin n) : ∃ c : Fin n, c ≠ i ∧ c ≠ j := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := by
    intro c _
    by_cases hc : c = i
    · simp [hc]
    · simp [h c hc]
  have h1 := Finset.card_le_card hsub
  have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- For `n ≥ 3` the minors with distinct columns have Haar mean zero. -/
theorem integral_minor2_haar (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (a b : Fin n) :
    ∫ X : SO n, minor2 a b i j (X : Matrix (Fin n) (Fin n) ℝ) ∂(haarSO n) = 0 := by
  obtain ⟨c, hci, hcj⟩ := exists_ne_ne hn i j
  have hmem : flipMat i * flipMat c ∈ specialOrthogonalGroup (Fin n) ℝ := by
    rw [mem_specialOrthogonalGroup_iff]
    refine ⟨mul_mem (flipMat_mem i) (flipMat_mem c), ?_⟩
    rw [det_mul, det_flipMat, det_flipMat]
    norm_num
  refine integral_eq_zero_of_mul_right_eq_neg (g := (⟨flipMat i * flipMat c, hmem⟩ : SO n))
    (fun X => ?_)
  show minor2 a b i j ((X : Matrix (Fin n) (Fin n) ℝ) * (flipMat i * flipMat c))
    = -minor2 a b i j (X : Matrix (Fin n) (Fin n) ℝ)
  rw [← mul_assoc]
  simp only [minor2, flipMat, mul_diagonal, ↓reduceIte, Ne.symm hij, Ne.symm hci, Ne.symm hcj]
  ring

/-- The principal minors have positive `L²(Haar)` norm. -/
theorem integral_minor2_sq_pos {i j : Fin n} (hij : i ≠ j) :
    0 < ∫ X : SO n, minor2 i j i j (X : Matrix (Fin n) (Fin n) ℝ) ^ 2 ∂(haarSO n) := by
  refine ((continuous_minor2 i j i j).pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun X => sq_nonneg _) (x := 1) ?_
  simp [minor2, hij, Ne.symm hij]

/-- **Theorem (a second upper bound on the spectral gap).** For `n ≥ 3` and a
conjugation-invariant step distribution `ν`, every Poincaré constant of the walk is at most
`1 - λ₂(ν)`, where `λ₂(ν) = E[R_{ii} R_{jj} - R_{ij} R_{ji}]`. -/
theorem gap_le_one_sub_minorEig (hn : 3 ≤ n) (ν : Measure (SO n)) [IsProbabilityMeasure ν]
    (hν : ConjInvariant ν) {i j : Fin n} (hij : i ≠ j) {γ : ℝ}
    (hγ : PoincareIneq (haarSO n) ν γ) : γ ≤ 1 - minorEig ν i j := by
  have hc := continuous_minor2 i j i j
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hmem : MemLp (fun X : SO n => minor2 i j i j (X : Matrix (Fin n) (Fin n) ℝ)) 2
      (haarSO n) :=
    MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun X => hC _ ⟨X, rfl⟩)
  exact hγ.le_of_eigenfunction hmem (integral_minor2_haar hn hij i j)
    (integral_minor2_sq_pos hij) (markovOp_minor2 ν hν hij i j)

/-! ### Independence of the pair -/

theorem conjO_perm_apply (σ : Equiv.Perm (Fin n))
    (hσ : σ.permMatrix ℝ ∈ orthogonalGroup (Fin n) ℝ) (R : SO n) (a b : Fin n) :
    (conjO ⟨σ.permMatrix ℝ, hσ⟩ R : Matrix (Fin n) (Fin n) ℝ) a b
      = (R : Matrix (Fin n) (Fin n) ℝ) (σ a) (σ b) := by
  simp only [coe_conjO, transpose_permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Equiv.Perm.inv_def]

theorem minorEig_swap (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    (p q i j : Fin n) :
    minorEig ν (Equiv.swap p q i) (Equiv.swap p q j) = minorEig ν i j := by
  have h := integral_conjO ν hν ⟨(Equiv.swap p q).permMatrix ℝ, swap_mem p q⟩
    (continuous_minor2 i j i j)
  simp only [minor2, conjO_perm_apply] at h
  simp only [minorEig, minor2]
  exact h

theorem minorEig_comm (ν : Measure (SO n)) (i j : Fin n) : minorEig ν i j = minorEig ν j i := by
  simp only [minorEig, minor2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun R => ?_)
  ring

/-- **`λ₂` does not depend on the pair of indices.** -/
theorem minorEig_eq (ν : Measure (SO n)) [IsFiniteMeasure ν] (hν : ConjInvariant ν)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) : minorEig ν i j = minorEig ν k l := by
  have h1 := minorEig_swap ν hν i k i j
  rw [Equiv.swap_apply_left] at h1
  have hj' : k ≠ Equiv.swap i k j := by
    intro h
    have h3 : Equiv.swap i k i = Equiv.swap i k j := by
      rw [Equiv.swap_apply_left]
      exact h
    exact hij ((Equiv.swap i k).injective h3)
  have h2 := minorEig_swap ν hν (Equiv.swap i k j) l k (Equiv.swap i k j)
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hj' hkl] at h2
  rw [← h1]
  exact h2.symm

end SOnMCMC

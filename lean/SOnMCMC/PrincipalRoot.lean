import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Order.MonotoneConvergence
import SOnMCMC.Projection

/-!
# The principal root: existence, the Newton iteration, and the sampler's move

Paper: Section 5.2.

For a skew-symmetric `A`, an orthogonal `R` with skew part `A` and positive semidefinite
symmetric part (the *principal root*) exists if and only if `1 + A²` is positive semidefinite,
and then it is `√(1 + A²) + A`.  This file proves:

* `tendsto_visser`: the iteration `P ← P - ½ (P² - B)`, `P₀ = 1`, converges to `√B` when
  `0 ≤ B ≤ 1`;
* `one_add_newtonFrozen`, `tendsto_newtonFrozen`, `posSemidef_of_tendsto_newtonFrozen`: Newton's
  method for the constraint `(1 + A + S)ᵀ (1 + A + S) = 1`, started at `S = 0` with the Jacobian
  frozen at the base point, is this iteration with `B = 1 + A²`; it converges if and only if
  `1 + A²` is positive semidefinite, and then to the principal root;
* `principalStep`: the group step of the sampler, `√(1 + A²) + A` if the root exists and `1`
  otherwise; it lies in `SO(n)`, is characterised by `eq_principalStep`, is conjugation
  equivariant (`principalStep_conj`) and measurable (`measurable_principalStep`);
* `isPrincipalProjection_iff`, `zhgMove_eq`: the move of the sampler of Zappa, Holmes-Cerfon and
  Goodman (projection, reverse check, Metropolis–Hastings test) is `X ↦ X · principalStep A`.
-/

open Matrix Filter Topology
open scoped MatrixOrder

namespace SOnMCMC

/-! ### The scalar iteration -/

/-- The iteration `p ← p - (p² - b)/2` started at `p = 1`. -/
noncomputable def visserS (b : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => visserS b k - (visserS b k ^ 2 - b) / 2

theorem visserS_bounds {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k : ℕ) :
    √b ≤ visserS b k ∧ visserS b k ≤ 1 := by
  have hs0 : 0 ≤ √b := Real.sqrt_nonneg b
  have hs1 : √b ≤ 1 := Real.sqrt_le_one.mpr hb1 |>.trans le_rfl
  have hs2 : √b ^ 2 = b := Real.sq_sqrt hb0
  induction k with
  | zero => exact ⟨hs1, le_rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [visserS]
    constructor
    · have : visserS b k - (visserS b k ^ 2 - b) / 2 - √b
          = (visserS b k - √b) * (1 - (visserS b k + √b) / 2) := by
        linear_combination (-1 / 2 : ℝ) * hs2
      have h3 : 0 ≤ (visserS b k - √b) * (1 - (visserS b k + √b) / 2) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    · nlinarith

theorem visserS_antitone {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : Antitone (visserS b) := by
  refine antitone_nat_of_succ_le fun k => ?_
  obtain ⟨h1, _⟩ := visserS_bounds hb0 hb1 k
  have hs0 : 0 ≤ √b := Real.sqrt_nonneg b
  have hs2 : √b ^ 2 = b := Real.sq_sqrt hb0
  simp only [visserS]
  nlinarith

/-- The scalar iteration converges to `√b` for `0 ≤ b ≤ 1`. -/
theorem tendsto_visserS {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Tendsto (visserS b) atTop (𝓝 (√b)) := by
  have hbdd : BddBelow (Set.range (visserS b)) :=
    ⟨√b, by rintro _ ⟨k, rfl⟩; exact (visserS_bounds hb0 hb1 k).1⟩
  have hlim := tendsto_atTop_ciInf (visserS_antitone hb0 hb1) hbdd
  set L := ⨅ i, visserS b i with hL
  have hL1 : Tendsto (fun k => visserS b (k + 1)) atTop (𝓝 L) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hL2 : Tendsto (fun k => visserS b (k + 1)) atTop (𝓝 (L - (L ^ 2 - b) / 2)) := by
    simp only [visserS]
    exact hlim.sub (((hlim.pow 2).sub_const b).div_const 2)
  have hfix := tendsto_nhds_unique hL1 hL2
  have hLs : √b ≤ L := le_ciInf fun k => (visserS_bounds hb0 hb1 k).1
  have hL0 : 0 ≤ L := (Real.sqrt_nonneg b).trans hLs
  have hsq : L ^ 2 = b := by linarith
  have : √b = L := by rw [← hsq, Real.sqrt_sq hL0]
  rw [this]
  exact hlim

/-! ### The matrix iteration -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The iteration `P ← P - ½ (P² - B)` started at `P = 1`. -/
noncomputable def visser (B : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => 1
  | k + 1 => visser B k - (1 / 2 : ℝ) • (visser B k * visser B k - B)

/-- Newton's method for `(1 + A + S)ᵀ (1 + A + S) = 1` in the symmetric unknown `S`, started at
`S = 0`, with the Jacobian frozen at the base point (where it is `dS ↦ 2 dS`). -/
noncomputable def newtonFrozen (A : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => 0
  | k + 1 => newtonFrozen A k
      - (1 / 2 : ℝ) • ((1 + A + newtonFrozen A k)ᵀ * (1 + A + newtonFrozen A k) - 1)

theorem visser_commute {B C : Matrix n n ℝ} (h : B * C = C * B) (k : ℕ) :
    visser B k * C = C * visser B k := by
  induction k with
  | zero => simp [visser]
  | succ k ih =>
    simp only [visser, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, ih, h]
    rw [← Matrix.mul_assoc (visser B k) C, ih, Matrix.mul_assoc]

theorem visser_transpose {B : Matrix n n ℝ} (hB : Bᵀ = B) (k : ℕ) :
    (visser B k)ᵀ = visser B k := by
  induction k with
  | zero => simp [visser]
  | succ k ih =>
    simp only [visser, transpose_sub, transpose_smul, transpose_mul, ih, hB]

/-- **The frozen Newton iteration is the square-root iteration** for `B = 1 + A²`. -/
theorem one_add_newtonFrozen {A : Matrix n n ℝ} (hA : Aᵀ = -A) (k : ℕ) :
    1 + newtonFrozen A k = visser (1 + A * A) k := by
  have hBt : (1 + A * A)ᵀ = 1 + A * A := by
    rw [transpose_add, transpose_one, transpose_mul, hA]
    simp
  have hBc : (1 + A * A) * A = A * (1 + A * A) := by
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
  induction k with
  | zero => simp [newtonFrozen, visser]
  | succ k ih =>
    have hc := visser_commute hBc k
    have ht := visser_transpose hBt k
    have e1 : 1 + A + newtonFrozen A k = visser (1 + A * A) k + A := by
      rw [← ih]
      abel
    have e2 : (visser (1 + A * A) k + A)ᵀ * (visser (1 + A * A) k + A)
        = visser (1 + A * A) k * visser (1 + A * A) k - A * A := by
      rw [transpose_add, ht, hA]
      simp only [add_mul, mul_add, neg_mul, hc]
      abel
    simp only [newtonFrozen, visser]
    rw [e1, e2, ← add_sub_assoc, ih]
    congr 2
    abel

theorem visser_diagonal (d : n → ℝ) (k : ℕ) :
    visser (diagonal d) k = diagonal (fun i => visserS (d i) k) := by
  induction k with
  | zero =>
    simp only [visser, visserS]
    exact diagonal_one.symm
  | succ k ih =>
    rw [visser, ih, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [visserS]
      ring
    · simp [hij]

theorem visser_conj (U : unitaryGroup n ℝ) (D : Matrix n n ℝ) (k : ℕ) :
    visser ((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ)) k
      = (U : Matrix n n ℝ) * visser D k * star (U : Matrix n n ℝ) := by
  have h1 : star (U : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 := Unitary.coe_star_mul_self U
  have h2 : (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 := Unitary.coe_mul_star_self U
  induction k with
  | zero => simp [visser, h2]
  | succ k ih =>
    have e : (U : Matrix n n ℝ) * visser D k * star (U : Matrix n n ℝ)
        * ((U : Matrix n n ℝ) * visser D k * star (U : Matrix n n ℝ))
        = (U : Matrix n n ℝ) * (visser D k * visser D k) * star (U : Matrix n n ℝ) := by
      calc (U : Matrix n n ℝ) * visser D k * star (U : Matrix n n ℝ)
            * ((U : Matrix n n ℝ) * visser D k * star (U : Matrix n n ℝ))
          = (U : Matrix n n ℝ) * visser D k
              * (star (U : Matrix n n ℝ) * (U : Matrix n n ℝ))
              * visser D k * star (U : Matrix n n ℝ) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [h1]
            simp only [Matrix.mul_assoc, Matrix.one_mul]
    simp only [visser]
    rw [ih, e]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The eigenvalues of `B` lie in `[0, 1]` when `0 ≤ B ≤ 1`, and `B` is diagonalised by an
orthogonal matrix. -/
theorem exists_diagonalization {B : Matrix n n ℝ} (hB : B.PosSemidef)
    (hB1 : (1 - B).PosSemidef) :
    ∃ (U : unitaryGroup n ℝ) (d : n → ℝ), (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧
      B = (U : Matrix n n ℝ) * diagonal d * star (U : Matrix n n ℝ) := by
  have hH := hB.isHermitian
  refine ⟨hH.eigenvectorUnitary, hH.eigenvalues, ?_, ?_⟩
  · have hspec : B = (hH.eigenvectorUnitary : Matrix n n ℝ) * diagonal hH.eigenvalues
        * star (hH.eigenvectorUnitary : Matrix n n ℝ) := by
      have := hH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at this
      simpa using this
    have h1 : (1 - B) = (hH.eigenvectorUnitary : Matrix n n ℝ)
        * diagonal (fun i => 1 - hH.eigenvalues i)
        * star (hH.eigenvectorUnitary : Matrix n n ℝ) := by
      have hU : (hH.eigenvectorUnitary : Matrix n n ℝ)
          * star (hH.eigenvectorUnitary : Matrix n n ℝ) = 1 := Unitary.coe_mul_star_self _
      have hd : diagonal (fun i => 1 - hH.eigenvalues i)
          = (1 : Matrix n n ℝ) - diagonal hH.eigenvalues := by
        rw [← diagonal_one, ← diagonal_sub]
      conv_lhs => rw [hspec]
      rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]
    have hpsd : (diagonal (fun i => 1 - hH.eigenvalues i)).PosSemidef := by
      rw [h1] at hB1
      exact (Unitary.isUnit_coe (U := hH.eigenvectorUnitary)).posSemidef_star_right_conjugate_iff.mp hB1
    intro i
    exact ⟨hH.posSemidef_iff_eigenvalues_nonneg.mp hB i,
      by have := posSemidef_diagonal_iff.mp hpsd i; linarith⟩
  · have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa using this

/-- **Convergence of the square-root iteration.** If `0 ≤ B ≤ 1` then
`P ← P - ½ (P² - B)`, `P₀ = 1`, converges to the positive semidefinite square root of `B`. -/
theorem tendsto_visser {B : Matrix n n ℝ} (hB : B.PosSemidef) (hB1 : (1 - B).PosSemidef) :
    Tendsto (visser B) atTop (𝓝 (CFC.sqrt B)) := by
  obtain ⟨U, d, hd, hBU⟩ := exists_diagonalization hB hB1
  have h1 : star (U : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 := Unitary.coe_star_mul_self U
  -- the limit
  set L : Matrix n n ℝ := (U : Matrix n n ℝ) * diagonal (fun i => √(d i))
    * star (U : Matrix n n ℝ) with hL
  have hLsq : L * L = B := by
    have : diagonal (fun i => √(d i)) * diagonal (fun i => √(d i)) = diagonal d := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      exact Real.mul_self_sqrt (hd i).1
    calc L * L = (U : Matrix n n ℝ) * diagonal (fun i => √(d i))
          * (star (U : Matrix n n ℝ) * (U : Matrix n n ℝ))
          * diagonal (fun i => √(d i)) * star (U : Matrix n n ℝ) := by
          simp only [hL, Matrix.mul_assoc]
      _ = (U : Matrix n n ℝ) * (diagonal (fun i => √(d i)) * diagonal (fun i => √(d i)))
          * star (U : Matrix n n ℝ) := by
          rw [h1]
          simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = B := by rw [this, hBU]
  have hLpsd : L.PosSemidef := by
    rw [hL]
    exact (Unitary.isUnit_coe (U := U)).posSemidef_star_right_conjugate_iff.mpr
      (posSemidef_diagonal_iff.mpr fun i => Real.sqrt_nonneg _)
  have hLeq : CFC.sqrt B = L := CFC.sqrt_unique hLsq hLpsd.nonneg
  rw [hLeq]
  have hk : ∀ k, visser B k = (U : Matrix n n ℝ) * diagonal (fun i => visserS (d i) k)
      * star (U : Matrix n n ℝ) := by
    intro k
    rw [hBU, visser_conj, visser_diagonal]
  have hcont : Continuous fun v : n → ℝ =>
      (U : Matrix n n ℝ) * diagonal v * star (U : Matrix n n ℝ) :=
    (continuous_const.matrix_mul continuous_id.matrix_diagonal).matrix_mul continuous_const
  have hv : Tendsto (fun k => fun i => visserS (d i) k) atTop (𝓝 fun i => √(d i)) :=
    tendsto_pi_nhds.mpr fun i => tendsto_visserS (hd i).1 (hd i).2
  have hfun : visser B = fun k => (U : Matrix n n ℝ) * diagonal (fun i => visserS (d i) k)
      * star (U : Matrix n n ℝ) := funext hk
  rw [hfun]
  exact (hcont.tendsto _).comp hv

/-! ### The principal root -/

theorem posSemidef_one_sub_of_skew {A : Matrix n n ℝ} (hA : Aᵀ = -A) :
    (1 - (1 + A * A)).PosSemidef := by
  have : 1 - (1 + A * A) = Aᴴ * A := by
    rw [conjTranspose_eq_transpose_of_trivial, hA]
    simp
  rw [this]
  exact posSemidef_conjTranspose_mul_self A

/-- For skew `A` with `1 + A² ≥ 0`: `√(1 + A²)` commutes with `A`. -/
theorem sqrt_commute_of_skew {A : Matrix n n ℝ} (hA : Aᵀ = -A)
    (hB : (1 + A * A).PosSemidef) :
    CFC.sqrt (1 + A * A) * A = A * CFC.sqrt (1 + A * A) := by
  have hBc : (1 + A * A) * A = A * (1 + A * A) := by
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
  have hlim := tendsto_visser hB (posSemidef_one_sub_of_skew hA)
  have hcR : Continuous fun M : Matrix n n ℝ => M * A := continuous_id.matrix_mul continuous_const
  have hcL : Continuous fun M : Matrix n n ℝ => A * M := continuous_const.matrix_mul continuous_id
  have h1 : Tendsto (fun k => visser (1 + A * A) k * A) atTop
      (𝓝 (CFC.sqrt (1 + A * A) * A)) := (hcR.tendsto _).comp hlim
  have h2 : Tendsto (fun k => visser (1 + A * A) k * A) atTop
      (𝓝 (A * CFC.sqrt (1 + A * A))) := by
    have := (hcL.tendsto _).comp hlim
    refine this.congr fun k => ?_
    exact (visser_commute hBc k).symm
  exact tendsto_nhds_unique h1 h2

/-- The group step of the sampler: the principal root `√(1 + A²) + A` if `A` is skew-symmetric
and `1 + A²` is positive semidefinite, and the identity (rejection) otherwise. -/
noncomputable def principalStep (A : Matrix n n ℝ) : Matrix n n ℝ :=
  open Classical in
  if Aᵀ = -A ∧ (1 + A * A).PosSemidef then CFC.sqrt (1 + A * A) + A else 1

theorem principalStep_of_not {A : Matrix n n ℝ} (h : ¬(Aᵀ = -A ∧ (1 + A * A).PosSemidef)) :
    principalStep A = 1 := by
  simp [principalStep, h]

theorem principalStep_of {A : Matrix n n ℝ} (hA : Aᵀ = -A) (hB : (1 + A * A).PosSemidef) :
    principalStep A = CFC.sqrt (1 + A * A) + A := by
  simp [principalStep, hA, hB]

/-- **The principal root exists when `1 + A² ≥ 0`:** it is orthogonal, has skew part `A` and
positive semidefinite symmetric part. -/
theorem principalStep_spec {A : Matrix n n ℝ} (hA : Aᵀ = -A) (hB : (1 + A * A).PosSemidef) :
    principalStep A ∈ orthogonalGroup n ℝ ∧ skewPart (principalStep A) = A ∧
      (symPart (principalStep A)).PosSemidef := by
  have hPpsd : (CFC.sqrt (1 + A * A)).PosSemidef := (CFC.sqrt_nonneg (1 + A * A)).posSemidef
  have hPt : (CFC.sqrt (1 + A * A))ᵀ = CFC.sqrt (1 + A * A) := by
    have := hPpsd.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hPP : CFC.sqrt (1 + A * A) * CFC.sqrt (1 + A * A) = 1 + A * A :=
    CFC.sqrt_mul_sqrt_self (1 + A * A) hB.nonneg
  rw [principalStep_of hA hB]
  refine ⟨add_mem_orthogonalGroup hPt hA (sqrt_commute_of_skew hA hB) hPP,
    skewPart_add_of_symm_of_skew hPt hA, ?_⟩
  rw [symPart_add_of_symm_of_skew hPt hA]
  exact hPpsd

theorem principalStep_mem_orthogonal (A : Matrix n n ℝ) :
    principalStep A ∈ orthogonalGroup n ℝ := by
  by_cases h : Aᵀ = -A ∧ (1 + A * A).PosSemidef
  · exact (principalStep_spec h.1 h.2).1
  · rw [principalStep_of_not h]
    exact one_mem _

theorem posSemidef_symPart_principalStep (A : Matrix n n ℝ) :
    (symPart (principalStep A)).PosSemidef := by
  by_cases h : Aᵀ = -A ∧ (1 + A * A).PosSemidef
  · exact (principalStep_spec h.1 h.2).2.2
  · rw [principalStep_of_not h]
    have : symPart (1 : Matrix n n ℝ) = 1 := by
      simp only [symPart, transpose_one]
      module
    rw [this]
    exact PosSemidef.one

/-- The group step is always a rotation. -/
theorem principalStep_mem (A : Matrix n n ℝ) : principalStep A ∈ specialOrthogonalGroup n ℝ :=
  mem_specialOrthogonalGroup_iff.mpr ⟨principalStep_mem_orthogonal A,
    det_eq_one_of_posSemidef (principalStep_mem_orthogonal A)
      (posSemidef_symPart_principalStep A)⟩

/-- **A principal root exists if and only if `1 + A² ≥ 0`.** -/
theorem exists_principal_iff {A : Matrix n n ℝ} (hA : Aᵀ = -A) :
    (∃ R ∈ orthogonalGroup n ℝ, skewPart R = A ∧ (symPart R).PosSemidef)
      ↔ (1 + A * A).PosSemidef := by
  constructor
  · rintro ⟨R, hR, hs, hp⟩
    have h := symPart_sq hR
    rw [hs] at h
    rw [← h]
    have : symPart R * symPart R = (symPart R)ᴴ * symPart R := by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_symPart]
    rw [this]
    exact posSemidef_conjTranspose_mul_self _
  · intro hB
    exact ⟨principalStep A, (principalStep_spec hA hB).1, (principalStep_spec hA hB).2.1,
      (principalStep_spec hA hB).2.2⟩

/-- **The principal root is `principalStep A`.** -/
theorem eq_principalStep {A R : Matrix n n ℝ} (hA : Aᵀ = -A) (hR : R ∈ orthogonalGroup n ℝ)
    (hs : skewPart R = A) (hp : (symPart R).PosSemidef) : R = principalStep A := by
  have hB : (1 + A * A).PosSemidef := (exists_principal_iff hA).mp ⟨R, hR, hs, hp⟩
  obtain ⟨h1, h2, h3⟩ := principalStep_spec hA hB
  exact principal_root_unique hR h1 (hs.trans h2.symm) hp h3

/-- The step for `-A` is the transpose (the inverse) of the step for `A`. -/
theorem principalStep_neg (A : Matrix n n ℝ) : principalStep (-A) = (principalStep A)ᵀ := by
  by_cases h : Aᵀ = -A ∧ (1 + A * A).PosSemidef
  · obtain ⟨hA, hB⟩ := h
    obtain ⟨h1, h2, h3⟩ := principalStep_spec hA hB
    have hA' : (-A)ᵀ = -(-A) := by rw [transpose_neg, hA]
    refine (eq_principalStep hA' ?_ ?_ ?_).symm
    · rw [mem_orthogonalGroup_iff, transpose_transpose]
      exact (mem_orthogonalGroup_iff' n ℝ).mp h1
    · rw [skewPart_transpose, h2]
    · rw [symPart_transpose]
      exact h3
  · have h' : ¬((-A)ᵀ = -(-A) ∧ (1 + -A * -A).PosSemidef) := by
      intro ⟨h1, h2⟩
      apply h
      refine ⟨?_, by simpa using h2⟩
      have := congrArg (fun M => -M) h1
      simpa [transpose_neg] using this
    rw [principalStep_of_not h, principalStep_of_not h', transpose_one]

/-- **Conjugation equivariance of the group step.** -/
theorem principalStep_conj {Q : Matrix n n ℝ} (hQ : Q ∈ orthogonalGroup n ℝ) (A : Matrix n n ℝ) :
    principalStep (Q * A * Qᵀ) = Q * principalStep A * Qᵀ := by
  have hQ1 := (mem_orthogonalGroup_iff n ℝ).mp hQ
  have hQ2 := (mem_orthogonalGroup_iff' n ℝ).mp hQ
  have hQt : Qᵀ ∈ orthogonalGroup n ℝ := by
    rw [mem_orthogonalGroup_iff, transpose_transpose]
    exact hQ2
  have key : ∀ A : Matrix n n ℝ, (Aᵀ = -A ∧ (1 + A * A).PosSemidef) →
      principalStep (Q * A * Qᵀ) = Q * principalStep A * Qᵀ := by
    intro A ⟨hA, hB⟩
    obtain ⟨h1, h2, h3⟩ := principalStep_spec hA hB
    have hA' : (Q * A * Qᵀ)ᵀ = -(Q * A * Qᵀ) := by
      simp only [transpose_mul, transpose_transpose, hA, Matrix.mul_assoc, Matrix.mul_neg,
        Matrix.neg_mul]
    refine (eq_principalStep hA' (mul_mem (mul_mem hQ h1) hQt) ?_ ?_).symm
    · rw [skewPart_conj, h2]
    · exact posSemidef_symPart_conj Q h3
  by_cases h : Aᵀ = -A ∧ (1 + A * A).PosSemidef
  · exact key A h
  · have h' : ¬((Q * A * Qᵀ)ᵀ = -(Q * A * Qᵀ) ∧
        (1 + Q * A * Qᵀ * (Q * A * Qᵀ)).PosSemidef) := by
      intro hc
      apply h
      -- conjugate back by `Qᵀ`
      have hback : Qᵀ * (Q * A * Qᵀ) * Q = A := by
        calc Qᵀ * (Q * A * Qᵀ) * Q = (Qᵀ * Q) * A * (Qᵀ * Q) := by
              simp only [Matrix.mul_assoc]
          _ = A := by rw [hQ2, Matrix.one_mul, Matrix.mul_one]
      have hc' := hc
      obtain ⟨hA', hB'⟩ := hc
      constructor
      · have := congrArg (fun M => Qᵀ * M * Q) hA'
        simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, Matrix.neg_mul] at this
        have e : Qᵀ * (Q * (Aᵀ * Qᵀ)) * Q = Aᵀ := by
          calc Qᵀ * (Q * (Aᵀ * Qᵀ)) * Q = (Qᵀ * Q) * Aᵀ * (Qᵀ * Q) := by
                simp only [Matrix.mul_assoc]
            _ = Aᵀ := by rw [hQ2, Matrix.one_mul, Matrix.mul_one]
        rw [e, hback] at this
        exact this
      · have e : 1 + A * A = Qᵀ * (1 + Q * A * Qᵀ * (Q * A * Qᵀ)) * Qᵀᵀ := by
          rw [transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQ2]
          congr 1
          calc A * A = (Qᵀ * Q) * A * (Qᵀ * Q) * A * (Qᵀ * Q) := by
                rw [hQ2]
                simp
            _ = Qᵀ * (Q * A * Qᵀ * (Q * A * Qᵀ)) * Q := by
                simp only [Matrix.mul_assoc]
        rw [e]
        have := hB'.mul_mul_conjTranspose_same Qᵀ
        rwa [conjTranspose_eq_transpose_of_trivial] at this
    rw [principalStep_of_not h, principalStep_of_not h', Matrix.mul_one, hQ1]

/-! ### Newton's method finds the principal root -/

/-- **Convergence of the frozen Newton iteration.** If `A` is skew-symmetric and `1 + A² ≥ 0`,
the iterates `1 + A + Sₖ` converge to the principal root. -/
theorem tendsto_newtonFrozen {A : Matrix n n ℝ} (hA : Aᵀ = -A) (hB : (1 + A * A).PosSemidef) :
    Tendsto (fun k => 1 + A + newtonFrozen A k) atTop (𝓝 (principalStep A)) := by
  have hlim := tendsto_visser hB (posSemidef_one_sub_of_skew hA)
  rw [principalStep_of hA hB]
  have := hlim.add_const A
  refine this.congr fun k => ?_
  rw [← one_add_newtonFrozen hA k]
  abel

/-- **Conversely**, if the frozen Newton iteration converges, then `1 + A² ≥ 0`: the iteration
converges exactly when the projection exists. -/
theorem posSemidef_of_tendsto_newtonFrozen {A S : Matrix n n ℝ} (hA : Aᵀ = -A)
    (h : Tendsto (newtonFrozen A) atTop (𝓝 S)) : (1 + A * A).PosSemidef := by
  have hBt : (1 + A * A)ᵀ = 1 + A * A := by
    rw [transpose_add, transpose_one, transpose_mul, hA]
    simp
  have hV : Tendsto (visser (1 + A * A)) atTop (𝓝 (1 + S)) := by
    have := h.const_add (1 : Matrix n n ℝ)
    exact this.congr fun k => one_add_newtonFrozen hA k
  -- the limit is symmetric and a fixed point of the iteration
  have hLt : (1 + S)ᵀ = 1 + S := by
    have hct : Continuous fun M : Matrix n n ℝ => Mᵀ := continuous_id.matrix_transpose
    have h1 : Tendsto (fun k => (visser (1 + A * A) k)ᵀ) atTop (𝓝 (1 + S)ᵀ) :=
      (hct.tendsto _).comp hV
    have h2 : Tendsto (fun k => (visser (1 + A * A) k)ᵀ) atTop (𝓝 (1 + S)) :=
      hV.congr fun k => (visser_transpose hBt k).symm
    exact tendsto_nhds_unique h1 h2
  have hfix : (1 + S) = (1 + S) - (1 / 2 : ℝ) • ((1 + S) * (1 + S) - (1 + A * A)) := by
    have h1 : Tendsto (fun k => visser (1 + A * A) (k + 1)) atTop (𝓝 (1 + S)) :=
      hV.comp (tendsto_add_atTop_nat 1)
    have hc0 : Continuous fun P : Matrix n n ℝ => P * P - (1 + A * A) :=
      (continuous_id.matrix_mul continuous_id).sub continuous_const
    have hc : Continuous fun P : Matrix n n ℝ =>
        P - (1 / 2 : ℝ) • (P * P - (1 + A * A)) :=
      continuous_id.sub (hc0.const_smul (1 / 2 : ℝ))
    have h2 : Tendsto (fun k => visser (1 + A * A) (k + 1)) atTop
        (𝓝 ((1 + S) - (1 / 2 : ℝ) • ((1 + S) * (1 + S) - (1 + A * A)))) :=
      (hc.tendsto _).comp hV
    exact tendsto_nhds_unique h1 h2
  have hsq : (1 + S) * (1 + S) = 1 + A * A := by
    have h0 : (1 / 2 : ℝ) • ((1 + S) * (1 + S) - (1 + A * A)) = 0 :=
      sub_eq_self.mp hfix.symm
    have h1 : (1 + S) * (1 + S) - (1 + A * A) = 0 :=
      (smul_eq_zero.mp h0).resolve_left (by norm_num)
    exact sub_eq_zero.mp h1
  rw [← hsq]
  have : (1 + S) * (1 + S) = (1 + S)ᴴ * (1 + S) := by
    rw [conjTranspose_eq_transpose_of_trivial, hLt]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

/-! ### The move of the sampler -/

/-- `Y` is a *principal projection* of the tangent proposal `X + X A`: it is orthogonal, it
differs from the proposal by a normal vector `X S` with `S` symmetric, and `Xᵀ Y` has positive
semidefinite symmetric part. -/
def IsPrincipalProjection (X A Y : Matrix n n ℝ) : Prop :=
  Y ∈ orthogonalGroup n ℝ ∧ (∃ S : Matrix n n ℝ, Sᵀ = S ∧ Y = X + X * A + X * S) ∧
    (symPart (Xᵀ * Y)).PosSemidef

/-- **The projection step.** A principal projection of `X + X A` exists if and only if
`1 + A² ≥ 0`, and then it is unique and equal to `X · principalStep A`. -/
theorem isPrincipalProjection_iff {X A Y : Matrix n n ℝ} (hX : X ∈ orthogonalGroup n ℝ)
    (hA : Aᵀ = -A) :
    IsPrincipalProjection X A Y ↔ (1 + A * A).PosSemidef ∧ Y = X * principalStep A := by
  have hX1 := (mem_orthogonalGroup_iff n ℝ).mp hX
  have hX2 := (mem_orthogonalGroup_iff' n ℝ).mp hX
  have hXt : Xᵀ ∈ orthogonalGroup n ℝ := by
    rw [mem_orthogonalGroup_iff, transpose_transpose]
    exact hX2
  constructor
  · rintro ⟨hY, hS, hp⟩
    have hs : skewPart (Xᵀ * Y) = A := (exists_normal_iff hX hA).mp hS
    have hR : Xᵀ * Y ∈ orthogonalGroup n ℝ := mul_mem hXt hY
    refine ⟨(exists_principal_iff hA).mp ⟨_, hR, hs, hp⟩, ?_⟩
    rw [← eq_principalStep hA hR hs hp, ← Matrix.mul_assoc, hX1, Matrix.one_mul]
  · rintro ⟨hB, rfl⟩
    obtain ⟨h1, h2, h3⟩ := principalStep_spec hA hB
    have e : Xᵀ * (X * principalStep A) = principalStep A := by
      rw [← Matrix.mul_assoc, hX2, Matrix.one_mul]
    refine ⟨mul_mem hX h1, (exists_normal_iff hX hA).mpr ?_, ?_⟩
    · rw [e]
      exact h2
    · rw [e]
      exact h3

/-- **The reverse move.** From `Y = X · principalStep A`, the tangent step of the reverse move
is `Y (-A)`, its principal projection is `X`, and it has the same length as the forward step. -/
theorem isPrincipalProjection_reverse {X A : Matrix n n ℝ} (hX : X ∈ orthogonalGroup n ℝ)
    (hA : Aᵀ = -A) (hB : (1 + A * A).PosSemidef) :
    skewPart ((X * principalStep A)ᵀ * X) = -A ∧
      IsPrincipalProjection (X * principalStep A) (-A) X ∧
      frobSq (X * principalStep A * -A) = frobSq (X * A) := by
  obtain ⟨h1, h2, h3⟩ := principalStep_spec hA hB
  have hY : X * principalStep A ∈ orthogonalGroup n ℝ := mul_mem hX h1
  have hA' : (-A)ᵀ = -(-A) := by rw [transpose_neg, hA]
  refine ⟨by rw [skewPart_reverse hX, h2], ?_, reverse_proposal_frobSq hX hY A⟩
  rw [isPrincipalProjection_iff hY hA']
  refine ⟨by simpa using hB, ?_⟩
  rw [principalStep_neg, Matrix.mul_assoc, (mem_orthogonalGroup_iff n ℝ).mp h1, Matrix.mul_one]

open Classical in
/-- **One move of the sampler of Zappa, Holmes-Cerfon and Goodman on the orthogonal group**, for
the uniform target and a tangent proposal whose density at `V` is `g (‖V‖²)`.

From `X`, with tangent proposal `X A` and a uniform random number `u`:
1. project `X + X A` to the group along the normal space at `X`; if there is no principal
   projection, stay at `X`;
2. compute the tangent step `Y A'` of the reverse move, `A' = skew(Yᵀ X)`, and check that its
   projection from `Y` is `X`; if not, stay at `X`;
3. accept `Y` if `u ≤ g(‖Y A'‖²) / g(‖X A‖²)`, the Metropolis–Hastings ratio for the uniform
   target; otherwise stay at `X`. -/
noncomputable def zhgMove (g : ℝ → ℝ) (X A : Matrix n n ℝ) (u : ℝ) : Matrix n n ℝ :=
  if h : ∃ Y, IsPrincipalProjection X A Y then
    if IsPrincipalProjection h.choose (skewPart (h.chooseᵀ * X)) X ∧
        u ≤ g (frobSq (h.choose * skewPart (h.chooseᵀ * X))) / g (frobSq (X * A)) then
      h.choose
    else X
  else X

/-- **The sampler's move is a group step.** For orthogonal `X`, skew-symmetric `A`, a positive
proposal density and `u ≤ 1`, the move is `X ↦ X · principalStep A`: the reverse check always
succeeds and the Metropolis–Hastings ratio is `1`. -/
theorem zhgMove_eq {g : ℝ → ℝ} (hg : ∀ r, 0 < g r) {X A : Matrix n n ℝ}
    (hX : X ∈ orthogonalGroup n ℝ) (hA : Aᵀ = -A) {u : ℝ} (hu : u ≤ 1) :
    zhgMove g X A u = X * principalStep A := by
  unfold zhgMove
  by_cases hB : (1 + A * A).PosSemidef
  · have hex : ∃ Y, IsPrincipalProjection X A Y :=
      ⟨_, (isPrincipalProjection_iff hX hA).mpr ⟨hB, rfl⟩⟩
    have hY : hex.choose = X * principalStep A :=
      ((isPrincipalProjection_iff hX hA).mp hex.choose_spec).2
    obtain ⟨r1, r2, r3⟩ := isPrincipalProjection_reverse hX hA hB
    rw [dite_eq_left_of_eq_true (eq_true hex), hY, r1, r3, div_self (hg _).ne',
      ite_eq_left_of_eq_true _ _ (eq_true ⟨r2, hu⟩)]
  · have hex : ¬∃ Y, IsPrincipalProjection X A Y := fun ⟨Y, hY⟩ =>
      hB ((isPrincipalProjection_iff hX hA).mp hY).1
    rw [dite_eq_right_of_eq_false (eq_false hex), principalStep_of_not (fun h => hB h.2),
      Matrix.mul_one]

/-! ### Measurability of the group step -/

theorem continuous_visser {α : Type*} [TopologicalSpace α] {f : α → Matrix n n ℝ}
    (hf : Continuous f) (k : ℕ) : Continuous fun a => visser (f a) k := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    simp only [visser]
    have h0 : Continuous fun a => visser (f a) k * visser (f a) k - f a :=
      (ih.matrix_mul ih).sub hf
    exact ih.sub (h0.const_smul (1 / 2 : ℝ))

theorem isClosed_principal_domain :
    IsClosed {A : Matrix n n ℝ | Aᵀ = -A ∧ (1 + A * A).PosSemidef} := by
  have h1 : IsClosed {A : Matrix n n ℝ | Aᵀ = -A} :=
    isClosed_eq continuous_id.matrix_transpose continuous_id.neg
  have h2 : IsClosed {A : Matrix n n ℝ | (1 + A * A).PosSemidef} := by
    have hc : Continuous fun A : Matrix n n ℝ => 1 + A * A :=
      continuous_const.add (continuous_id.matrix_mul continuous_id)
    exact Matrix.posSemidef_is_closed.preimage hc
  exact h1.inter h2

/-- **The group step is a measurable function of the tangent proposal.** -/
theorem measurable_principalStep :
    Measurable (principalStep : Matrix n n ℝ → Matrix n n ℝ) := by
  classical
  have hpm : TopologicalSpace.PseudoMetrizableSpace (Matrix n n ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (n → n → ℝ))
  set g : ℕ → Matrix n n ℝ → Matrix n n ℝ := fun k A =>
    if Aᵀ = -A ∧ (1 + A * A).PosSemidef then visser (1 + A * A) k + A else 1 with hg
  have hmeas : ∀ k, Measurable (g k) := by
    intro k
    refine Measurable.ite isClosed_principal_domain.measurableSet ?_ measurable_const
    exact ((continuous_visser (continuous_const.add
      (continuous_id.matrix_mul continuous_id)) k).add continuous_id).measurable
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr fun A => ?_)
  by_cases h : Aᵀ = -A ∧ (1 + A * A).PosSemidef
  · have hlim := tendsto_visser h.2 (posSemidef_one_sub_of_skew h.1)
    simp only [hg, h, and_self, ↓reduceIte, principalStep_of h.1 h.2]
    exact hlim.add_const A
  · simp only [hg, h, ↓reduceIte, principalStep_of_not h]
    exact tendsto_const_nhds

end SOnMCMC

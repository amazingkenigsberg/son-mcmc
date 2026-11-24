import Mathlib.Analysis.Matrix.Order

/-!
# Algebra of the tangent-step-then-project move on the orthogonal group

Paper: Section 5.1.

The constraint manifold is `O(n) = {X : Xᵀ X = 1}` (with `SO(n)` its identity component).  At a
point `X`, the tangent space is `{X A : Aᵀ = -A}` and the normal space is `{X S : Sᵀ = S}`.  A
move of the sampler is `Y = X + X A + X S` with `Y` orthogonal.  This file proves the algebraic
facts behind the reduction of the sampler to a random walk on the group:

* `exists_normal_iff`: `Y` is such a move iff `R = Xᵀ Y` has skew part `A`, i.e. `Y = X R`;
* `symPart_mul_skewPart_comm`, `symPart_sq`: the symmetric part `P` of an orthogonal `R`
  commutes with its skew part `A`, and `P² = 1 + A²`; conversely `add_mem_orthogonalGroup`;
* `skewPart_reverse`, `reverse_proposal_frobSq`: the reverse move uses the tangent step `-A`,
  of the same length, so the Metropolis–Hastings ratio for the uniform target is `1`;
* `det_eq_one_of_posSemidef`: the principal root (`P` positive semidefinite) lies in `SO(n)`;
* `frobSq_one_sub`, `frobSq_skewPart_le`, `frobSq_one_sub_le`:
  `‖A‖² ≤ ‖1 - R‖² = 2 (n - tr R) ≤ 2 ‖A‖²` for the principal root.
-/

open Matrix

namespace SOnMCMC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric part `(R + Rᵀ)/2`. -/
noncomputable def symPart (R : Matrix n n ℝ) : Matrix n n ℝ := (1 / 2 : ℝ) • (R + Rᵀ)

/-- The skew-symmetric part `(R - Rᵀ)/2`. -/
noncomputable def skewPart (R : Matrix n n ℝ) : Matrix n n ℝ := (1 / 2 : ℝ) • (R - Rᵀ)

/-- The squared Frobenius norm `∑ᵢⱼ Mᵢⱼ²`. -/
def frobSq (M : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

omit [Fintype n] [DecidableEq n] in
theorem symPart_add_skewPart (R : Matrix n n ℝ) : symPart R + skewPart R = R := by
  simp only [symPart, skewPart]
  module

omit [Fintype n] [DecidableEq n] in
theorem transpose_symPart (R : Matrix n n ℝ) : (symPart R)ᵀ = symPart R := by
  simp only [symPart, transpose_smul, transpose_add, transpose_transpose]
  module

omit [Fintype n] [DecidableEq n] in
theorem transpose_skewPart (R : Matrix n n ℝ) : (skewPart R)ᵀ = -skewPart R := by
  simp only [skewPart, transpose_smul, transpose_sub, transpose_transpose]
  module

omit [Fintype n] [DecidableEq n] in
theorem skewPart_transpose (R : Matrix n n ℝ) : skewPart Rᵀ = -skewPart R := by
  simp only [skewPart, transpose_transpose]
  module

omit [Fintype n] [DecidableEq n] in
theorem skewPart_add_of_symm_of_skew {P A : Matrix n n ℝ} (hP : Pᵀ = P) (hA : Aᵀ = -A) :
    skewPart (P + A) = A := by
  simp only [skewPart, transpose_add, hP, hA]
  module

omit [Fintype n] [DecidableEq n] in
theorem symPart_add_of_symm_of_skew {P A : Matrix n n ℝ} (hP : Pᵀ = P) (hA : Aᵀ = -A) :
    symPart (P + A) = P := by
  simp only [symPart, transpose_add, hP, hA]
  module

omit [DecidableEq n] in
theorem frobSq_eq_trace (M : Matrix n n ℝ) : frobSq M = (Mᵀ * M).trace := by
  simp only [frobSq, trace, diag_apply, mul_apply, transpose_apply, pow_two]
  exact Finset.sum_comm

omit [DecidableEq n] in
theorem frobSq_nonneg (M : Matrix n n ℝ) : 0 ≤ frobSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq n] in
theorem frobSq_neg (M : Matrix n n ℝ) : frobSq (-M) = frobSq M := by
  simp [frobSq]

/-! ### Structure of orthogonal matrices: symmetric and skew parts -/

/-- For an orthogonal matrix, the symmetric and skew parts commute. -/
theorem symPart_mul_skewPart_comm {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) :
    symPart R * skewPart R = skewPart R * symPart R := by
  have h1 := (mem_orthogonalGroup_iff n ℝ).mp hR
  have h2 := (mem_orthogonalGroup_iff' n ℝ).mp hR
  simp only [symPart, skewPart, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub,
    sub_mul, h1, h2]
  module

/-- For an orthogonal matrix with symmetric part `P` and skew part `A`: `P² = 1 + A²`. -/
theorem symPart_sq {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) :
    symPart R * symPart R = 1 + skewPart R * skewPart R := by
  have h1 := (mem_orthogonalGroup_iff n ℝ).mp hR
  have h2 := (mem_orthogonalGroup_iff' n ℝ).mp hR
  simp only [symPart, skewPart, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub,
    sub_mul, h1, h2]
  module

/-- Conversely, a symmetric `P` and a skew `A` that commute and satisfy `P² = 1 + A²` assemble
into an orthogonal matrix `P + A`. -/
theorem add_mem_orthogonalGroup {P A : Matrix n n ℝ} (hP : Pᵀ = P) (hA : Aᵀ = -A)
    (hc : P * A = A * P) (hsq : P * P = 1 + A * A) : P + A ∈ orthogonalGroup n ℝ := by
  rw [mem_orthogonalGroup_iff, transpose_add, hP, hA]
  simp only [mul_add, add_mul, mul_neg, hc, hsq]
  abel

/-! ### The projection step is a group step -/

/-- **The move is a right multiplication.** Let `X` be orthogonal and `A` skew-symmetric.  A
matrix `Y` is of the form `X + X A + X S` with `S` symmetric (tangent step `X A` followed by a
correction `X S` in the normal space at `X`) if and only if `R = Xᵀ Y` has skew part `A`. -/
theorem exists_normal_iff {X Y A : Matrix n n ℝ} (hX : X ∈ orthogonalGroup n ℝ)
    (hA : Aᵀ = -A) :
    (∃ S : Matrix n n ℝ, Sᵀ = S ∧ Y = X + X * A + X * S) ↔ skewPart (Xᵀ * Y) = A := by
  have h1 := (mem_orthogonalGroup_iff n ℝ).mp hX
  have h2 := (mem_orthogonalGroup_iff' n ℝ).mp hX
  constructor
  · rintro ⟨S, hS, rfl⟩
    have : Xᵀ * (X + X * A + X * S) = 1 + A + S := by
      simp only [mul_add, ← mul_assoc, h2, one_mul]
    rw [this]
    simp only [skewPart, transpose_add, transpose_one, hA, hS]
    module
  · intro h
    have h2A : Xᵀ * Y - (Xᵀ * Y)ᵀ = (2 : ℝ) • A := by
      rw [← h]
      simp only [skewPart]
      module
    refine ⟨Xᵀ * Y - 1 - A, ?_, ?_⟩
    · have ht : (Xᵀ * Y)ᵀ = Xᵀ * Y - (2 : ℝ) • A := by
        rw [← h2A]
        abel
      rw [transpose_sub, transpose_sub, transpose_one, hA, ht]
      module
    · have : X * (Xᵀ * Y - 1 - A) = Y - X - X * A := by
        simp only [mul_sub, mul_one, ← mul_assoc, h1, one_mul]
      rw [this]
      abel

/-- **The reverse move.** If `Y = X R`, then going back from `Y` to `X` is the group step `Rᵀ`,
whose skew part is `-A`. -/
theorem skewPart_reverse {X : Matrix n n ℝ} (hX : X ∈ orthogonalGroup n ℝ) (R : Matrix n n ℝ) :
    skewPart ((X * R)ᵀ * X) = -skewPart R := by
  have h2 := (mem_orthogonalGroup_iff' n ℝ).mp hX
  rw [transpose_mul, mul_assoc, h2, mul_one, skewPart_transpose]

/-- Left multiplication by an orthogonal matrix preserves the Frobenius norm. -/
theorem frobSq_orthogonal_mul {X : Matrix n n ℝ} (hX : X ∈ orthogonalGroup n ℝ)
    (M : Matrix n n ℝ) : frobSq (X * M) = frobSq M := by
  have h2 := (mem_orthogonalGroup_iff' n ℝ).mp hX
  rw [frobSq_eq_trace, frobSq_eq_trace, transpose_mul, mul_assoc, ← mul_assoc Xᵀ, h2, one_mul]

/-- **Forward and reverse tangent proposals have the same length.** Hence any proposal density
that depends only on the length of the tangent step gives Metropolis–Hastings ratio `1` for the
uniform target. -/
theorem reverse_proposal_frobSq {X Y : Matrix n n ℝ} (hX : X ∈ orthogonalGroup n ℝ)
    (hY : Y ∈ orthogonalGroup n ℝ) (A : Matrix n n ℝ) :
    frobSq (Y * (-A)) = frobSq (X * A) := by
  rw [frobSq_orthogonal_mul hY, frobSq_orthogonal_mul hX, frobSq_neg]

/-! ### The principal root stays in `SO(n)` -/

/-- An orthogonal matrix whose symmetric part is positive semidefinite has determinant `1`. -/
theorem det_eq_one_of_posSemidef {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ)
    (hP : (symPart R).PosSemidef) : R.det = 1 := by
  have h1 := (mem_orthogonalGroup_iff n ℝ).mp hR
  have hdet : R.det * R.det = 1 := by
    have := congrArg det h1
    rwa [det_mul, det_transpose, det_one] at this
  rcases mul_self_eq_one_iff.mp hdet with h | h
  · exact h
  · exfalso
    have hz : (1 + R).det = 0 := by
      have e : 1 + R = R * (1 + R)ᵀ := by
        rw [transpose_add, transpose_one, mul_add, mul_one, h1, add_comm]
      have := congrArg det e
      rw [det_mul, det_transpose, h] at this
      linarith
    obtain ⟨v, hv, hRv⟩ := exists_mulVec_eq_zero_iff.mpr hz
    have hRv' : R *ᵥ v = -v := by
      have : (1 + R) *ᵥ v = v + R *ᵥ v := by rw [add_mulVec, one_mulVec]
      rw [this] at hRv
      exact eq_neg_of_add_eq_zero_right hRv
    have hpsd := hP.dotProduct_mulVec_nonneg v
    have hs : star v = v := by
      ext i
      simp
    have h3 : v ⬝ᵥ (Rᵀ *ᵥ v) = v ⬝ᵥ (R *ᵥ v) := by
      rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
    have key : star v ⬝ᵥ (symPart R *ᵥ v) = -(v ⬝ᵥ v) := by
      rw [hs]
      simp only [symPart, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, smul_eq_mul,
        h3, hRv', dotProduct_neg]
      ring
    rw [key] at hpsd
    have hpos : 0 < v ⬝ᵥ v := by
      have h0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
      rcases h0.eq_or_lt with h0 | h0
      · exact absurd (dotProduct_self_eq_zero.mp h0.symm) hv
      · exact h0
    linarith

/-! ### Size of the step -/

/-- `‖1 - R‖² = 2 (n - tr R)` for an orthogonal matrix. -/
theorem frobSq_one_sub {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) :
    frobSq (1 - R) = 2 * ((Fintype.card n : ℝ) - R.trace) := by
  have h2 := (mem_orthogonalGroup_iff' n ℝ).mp hR
  rw [frobSq_eq_trace, transpose_sub, transpose_one]
  have : (1 - Rᵀ) * (1 - R) = 1 - R - Rᵀ + Rᵀ * R := by noncomm_ring
  rw [this, h2]
  simp only [trace_add, trace_sub, trace_one, trace_transpose]
  ring

omit [DecidableEq n] in
theorem trace_symPart (R : Matrix n n ℝ) : (symPart R).trace = R.trace := by
  simp only [symPart, trace_smul, trace_add, trace_transpose, smul_eq_mul]
  ring

/-- `‖A‖² = n - tr(P²)` for the skew part `A` and symmetric part `P` of an orthogonal matrix. -/
theorem frobSq_skewPart {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) :
    frobSq (skewPart R) = (Fintype.card n : ℝ) - (symPart R * symPart R).trace := by
  rw [frobSq_eq_trace, transpose_skewPart, symPart_sq hR]
  simp only [neg_mul, trace_neg, trace_add, trace_one]
  ring

/-- Pythagoras: `‖1 - R‖² = ‖A‖² + ‖1 - P‖²`. -/
theorem frobSq_one_sub_eq {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) :
    frobSq (1 - R) = frobSq (skewPart R) + frobSq (1 - symPart R) := by
  rw [frobSq_one_sub hR, frobSq_skewPart hR, frobSq_eq_trace (1 - symPart R), transpose_sub,
    transpose_one, transpose_symPart, ← trace_symPart R]
  have : (1 - symPart R) * (1 - symPart R)
      = 1 - symPart R - symPart R + symPart R * symPart R := by noncomm_ring
  rw [this]
  simp only [trace_add, trace_sub, trace_one]
  ring

/-- **Lower bound on the displacement:** `‖A‖² ≤ ‖1 - R‖²`. -/
theorem frobSq_skewPart_le {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) :
    frobSq (skewPart R) ≤ frobSq (1 - R) := by
  rw [frobSq_one_sub_eq hR]
  linarith [frobSq_nonneg (1 - symPart R)]

/-- For the principal root, `tr(P²) ≤ tr(P)`. -/
theorem trace_symPart_sq_le {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ)
    (hP : (symPart R).PosSemidef) : (symPart R * symPart R).trace ≤ (symPart R).trace := by
  have hPt : (symPart R)ᵀ = symPart R := transpose_symPart R
  have hAt : (skewPart R)ᵀ = -skewPart R := transpose_skewPart R
  have hc := symPart_mul_skewPart_comm hR
  have hsq := symPart_sq hR
  have hAA : skewPart R * skewPart R = symPart R * symPart R - 1 := by
    rw [hsq]
    abel
  have e1 : (1 - symPart R)ᵀ * symPart R * (1 - symPart R)
      = symPart R - symPart R * symPart R - symPart R * symPart R
        + symPart R * symPart R * symPart R := by
    rw [transpose_sub, transpose_one, hPt]
    noncomm_ring
  have e2 : skewPart R * symPart R * (skewPart R)ᵀ
      = symPart R - symPart R * symPart R * symPart R := by
    rw [hAt, ← hc, mul_neg, mul_assoc, hAA]
    noncomm_ring
  have hpsd1 : 0 ≤ ((1 - symPart R)ᵀ * symPart R * (1 - symPart R)).trace := by
    have := (hP.conjTranspose_mul_mul_same (1 - symPart R)).trace_nonneg
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hpsd2 : 0 ≤ (skewPart R * symPart R * (skewPart R)ᵀ).trace := by
    have := (hP.mul_mul_conjTranspose_same (skewPart R)).trace_nonneg
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [e1] at hpsd1
  rw [e2] at hpsd2
  simp only [trace_add, trace_sub] at hpsd1 hpsd2
  linarith

/-- **Upper bound on the displacement for the principal root:** `‖1 - R‖² ≤ 2 ‖A‖²`. -/
theorem frobSq_one_sub_le {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ)
    (hP : (symPart R).PosSemidef) : frobSq (1 - R) ≤ 2 * frobSq (skewPart R) := by
  rw [frobSq_one_sub hR, frobSq_skewPart hR, ← trace_symPart R]
  linarith [trace_symPart_sq_le hR hP]

/-- Summary: for the principal root, `½ ‖A‖² ≤ n - tr R ≤ ‖A‖²`. -/
theorem card_sub_trace_bounds {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ)
    (hP : (symPart R).PosSemidef) :
    frobSq (skewPart R) / 2 ≤ (Fintype.card n : ℝ) - R.trace ∧
      (Fintype.card n : ℝ) - R.trace ≤ frobSq (skewPart R) := by
  have h1 := frobSq_skewPart_le hR
  have h2 := frobSq_one_sub_le hR hP
  rw [frobSq_one_sub hR] at h1 h2
  constructor <;> linarith

/-! ### The principal root is unique and conjugation equivariant -/

omit [Fintype n] [DecidableEq n] in
theorem symPart_transpose (R : Matrix n n ℝ) : symPart Rᵀ = symPart R := by
  simp only [symPart, transpose_transpose]
  module

/-- The reverse group step `Rᵀ` has the same symmetric part as `R`, so the reverse projection is
again the principal one. -/
theorem symPart_reverse {X : Matrix n n ℝ} (hX : X ∈ orthogonalGroup n ℝ) (R : Matrix n n ℝ) :
    symPart ((X * R)ᵀ * X) = symPart R := by
  have h2 := (mem_orthogonalGroup_iff' n ℝ).mp hX
  rw [transpose_mul, mul_assoc, h2, mul_one, symPart_transpose]

omit [DecidableEq n] in
theorem skewPart_conj (Q R : Matrix n n ℝ) : skewPart (Q * R * Qᵀ) = Q * skewPart R * Qᵀ := by
  simp only [skewPart, transpose_mul, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
theorem symPart_conj (Q R : Matrix n n ℝ) : symPart (Q * R * Qᵀ) = Q * symPart R * Qᵀ := by
  simp only [symPart, transpose_mul, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Conjugation preserves positive semidefiniteness of the symmetric part. -/
theorem posSemidef_symPart_conj (Q : Matrix n n ℝ) {R : Matrix n n ℝ}
    (hP : (symPart R).PosSemidef) : (symPart (Q * R * Qᵀ)).PosSemidef := by
  rw [symPart_conj]
  have := hP.mul_mul_conjTranspose_same Q
  rwa [conjTranspose_eq_transpose_of_trivial] at this

open scoped MatrixOrder in
/-- A positive semidefinite matrix is determined by its square. -/
theorem posSemidef_eq_of_mul_self_eq {P₁ P₂ : Matrix n n ℝ} (h₁ : P₁.PosSemidef)
    (h₂ : P₂.PosSemidef) (h : P₁ * P₁ = P₂ * P₂) : P₁ = P₂ := by
  have e1 := CFC.sqrt_unique (a := P₂ * P₂) (b := P₁) h h₁.nonneg
  have e2 := CFC.sqrt_unique (a := P₂ * P₂) (b := P₂) rfl h₂.nonneg
  rw [← e1, e2]

/-- **Uniqueness of the principal root.** Two orthogonal matrices with the same skew part and
positive semidefinite symmetric parts are equal: the accepted move is a function of the tangent
proposal. -/
theorem principal_root_unique {R₁ R₂ : Matrix n n ℝ} (h₁ : R₁ ∈ orthogonalGroup n ℝ)
    (h₂ : R₂ ∈ orthogonalGroup n ℝ) (hs : skewPart R₁ = skewPart R₂)
    (hp₁ : (symPart R₁).PosSemidef) (hp₂ : (symPart R₂).PosSemidef) : R₁ = R₂ := by
  have hP : symPart R₁ = symPart R₂ :=
    posSemidef_eq_of_mul_self_eq hp₁ hp₂ (by rw [symPart_sq h₁, symPart_sq h₂, hs])
  rw [← symPart_add_skewPart R₁, ← symPart_add_skewPart R₂, hP, hs]

/-- The skew part of an orthogonal matrix has squared Frobenius norm at most `n`: a tangent
proposal longer than that has no projection at all. -/
theorem frobSq_skewPart_le_card {R : Matrix n n ℝ} (hR : R ∈ orthogonalGroup n ℝ) :
    frobSq (skewPart R) ≤ Fintype.card n := by
  rw [frobSq_skewPart hR]
  have h : 0 ≤ (symPart R * symPart R).trace := by
    have := frobSq_nonneg (symPart R)
    rwa [frobSq_eq_trace, transpose_symPart] at this
  linarith

end SOnMCMC

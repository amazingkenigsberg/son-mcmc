import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The normal form of a rotation

Every `R ∈ SO(N)` is conjugate, by an element of `SO(N)`, to a block-diagonal matrix
`t(θ)` with `2 × 2` rotation blocks `R_{θ_k}` in the coordinate planes `{2k, 2k+1}`, `k < N/2`,
followed by a `1` if `N` is odd (`exists_torusMat_conj`).

The proof is by strong induction on `N`.  Let `S = R + Rᵀ`, which is symmetric.  If `S` has an
eigenvector `v` with eigenvalue `2 cos θ`, `0 < θ < π`, then `span {v, R v}` is an invariant plane
on which `R` is a rotation by `θ`; if `S v = 2 v` then `R v = v`; and if every eigenvalue of `S` is
`-2` then `R = -1`.  In each case one extends to an orthonormal basis and recurses on the
orthogonal complement.
-/

open Matrix Real Finset

namespace SOnMCMC

/-! ### The block rotation `t(θ)` -/

/-- `t(θ)`: rotation by `θ k` in the coordinate plane `{2k, 2k+1}` for `k < N/2`, and `1` in the
last coordinate if `N` is odd.  Angles are indexed by `ℕ`; only `θ 0, …, θ (N/2 - 1)` are used. -/
noncomputable def torusMat (N : ℕ) (θ : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  if (i : ℕ) / 2 < N / 2 ∧ (i : ℕ) / 2 = (j : ℕ) / 2 then
    if (i : ℕ) % 2 = 0 then (if (j : ℕ) % 2 = 0 then cos (θ ((i : ℕ) / 2)) else -sin (θ ((i : ℕ) / 2)))
    else (if (j : ℕ) % 2 = 0 then sin (θ ((i : ℕ) / 2)) else cos (θ ((i : ℕ) / 2)))
  else if i = j then 1 else 0

section Peel

variable {M : ℕ} (θ : ℕ → ℝ)

theorem torusMat_succ_succ (i j : Fin M) :
    torusMat (M + 2) θ i.succ.succ j.succ.succ = torusMat M (fun k => θ (k + 1)) i j := by
  have hi : ((i.succ.succ : Fin (M + 2)) : ℕ) = (i : ℕ) + 2 := by simp
  have hj : ((j.succ.succ : Fin (M + 2)) : ℕ) = (j : ℕ) + 2 := by simp
  have h1 : ((i : ℕ) + 2) / 2 = (i : ℕ) / 2 + 1 := by omega
  have h2 : ((j : ℕ) + 2) / 2 = (j : ℕ) / 2 + 1 := by omega
  have h3 : (M + 2) / 2 = M / 2 + 1 := by omega
  have h4 : ((i : ℕ) + 2) % 2 = (i : ℕ) % 2 := by omega
  have h5 : ((j : ℕ) + 2) % 2 = (j : ℕ) % 2 := by omega
  have hij : (i.succ.succ = j.succ.succ) ↔ i = j := by simp
  simp only [torusMat, hi, hj, h1, h2, h3, h4, h5, hij, add_lt_add_iff_right, add_left_inj]

theorem torusMat_zero_zero : torusMat (M + 2) θ 0 0 = cos (θ 0) := by
  simp [torusMat]

theorem torusMat_zero_one : torusMat (M + 2) θ 0 1 = -sin (θ 0) := by
  simp [torusMat]

theorem torusMat_one_zero : torusMat (M + 2) θ 1 0 = sin (θ 0) := by
  simp [torusMat]

theorem torusMat_one_one : torusMat (M + 2) θ 1 1 = cos (θ 0) := by
  simp [torusMat]

theorem torusMat_zero_succ_succ (j : Fin M) : torusMat (M + 2) θ 0 j.succ.succ = 0 := by
  have hj : ((j.succ.succ : Fin (M + 2)) : ℕ) = (j : ℕ) + 2 := by simp
  have h : ¬ (0 = ((j : ℕ) + 2) / 2) := by omega
  simp [torusMat, h, Fin.ext_iff]

theorem torusMat_one_succ_succ (j : Fin M) : torusMat (M + 2) θ 1 j.succ.succ = 0 := by
  have hj : ((j.succ.succ : Fin (M + 2)) : ℕ) = (j : ℕ) + 2 := by simp
  have h : ¬ (1 / 2 = ((j : ℕ) + 2) / 2) := by omega
  have h' : ¬ ((1 : Fin (M + 2)) = j.succ.succ) := by
    intro e; have := congrArg Fin.val e; simp at this
  simp [torusMat, h, h']

theorem torusMat_succ_succ_zero (i : Fin M) : torusMat (M + 2) θ i.succ.succ 0 = 0 := by
  have hi : ((i.succ.succ : Fin (M + 2)) : ℕ) = (i : ℕ) + 2 := by simp
  have h : ¬ (((i : ℕ) + 2) / 2 = 0) := by omega
  simp [torusMat, h, Fin.ext_iff]

theorem torusMat_succ_succ_one (i : Fin M) : torusMat (M + 2) θ i.succ.succ 1 = 0 := by
  have hi : ((i.succ.succ : Fin (M + 2)) : ℕ) = (i : ℕ) + 2 := by simp
  have h : ¬ (((i : ℕ) + 2) / 2 = 1 / 2) := by omega
  have h' : ¬ (i.succ.succ = (1 : Fin (M + 2))) := by
    intro e; have := congrArg Fin.val e; simp at this
  simp [torusMat, h, h']

/-- The last coordinate: if `M` is odd we require the angle of the new last plane to be `0`. -/
theorem torusMat_castSucc (hθ : M % 2 = 1 → θ (M / 2) = 0) (i j : Fin M) :
    torusMat (M + 1) θ i.castSucc j.castSucc = torusMat M θ i j := by
  simp only [torusMat, Fin.val_castSucc, Fin.castSucc_inj]
  rcases Nat.even_or_odd M with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h1 : (M + 1) / 2 = M / 2 := by omega
    rw [h1]
  · have hθ' := hθ (by omega)
    have hM : M / 2 = r := by omega
    rw [hM] at hθ'
    by_cases hi : (i : ℕ) / 2 < M / 2
    · have : (i : ℕ) / 2 < (M + 1) / 2 := by omega
      simp [hi, this]
    · have hi2 : (i : ℕ) = M - 1 := by have := i.isLt; omega
      by_cases hj : (i : ℕ) / 2 = (j : ℕ) / 2
      · have hj2 : (j : ℕ) = M - 1 := by have := j.isLt; omega
        have hij : i = j := Fin.ext (by omega)
        subst hij
        have hlt : (i : ℕ) / 2 < (M + 1) / 2 := by omega
        have hpar : (i : ℕ) % 2 = 0 := by omega
        have hidx : (i : ℕ) / 2 = r := by omega
        simp [hpar, hidx, hθ']
      · simp [hi, hj]

theorem torusMat_last_castSucc (hθ : M % 2 = 1 → θ (M / 2) = 0) (j : Fin M) :
    torusMat (M + 1) θ (Fin.last M) j.castSucc = 0 := by
  have hne : Fin.last M ≠ j.castSucc := (Fin.castSucc_lt_last j).ne'
  have hj := j.isLt
  simp only [torusMat, Fin.val_last, Fin.val_castSucc, hne, ite_false]
  split_ifs with h h2 h3 <;>
    first | omega | (rw [hθ (by omega)]; simp) | rfl

theorem torusMat_castSucc_last (hθ : M % 2 = 1 → θ (M / 2) = 0) (i : Fin M) :
    torusMat (M + 1) θ i.castSucc (Fin.last M) = 0 := by
  have hne : i.castSucc ≠ Fin.last M := (Fin.castSucc_lt_last i).ne
  have hi := i.isLt
  simp only [torusMat, Fin.val_last, Fin.val_castSucc, hne, ite_false]
  split_ifs with h h2 h3 <;>
    first | omega | (rw [show (i : ℕ) / 2 = M / 2 by omega, hθ (by omega)]; simp) | rfl

theorem torusMat_last_last (hθ : M % 2 = 1 → θ (M / 2) = 0) :
    torusMat (M + 1) θ (Fin.last M) (Fin.last M) = 1 := by
  simp only [torusMat, Fin.val_last, ite_true]
  split_ifs with h h2 <;>
    first | omega | (rw [hθ (by omega)]; simp) | rfl

end Peel

/-- For even `N`, `t(π, …, π) = -1`. -/
theorem torusMat_pi {N : ℕ} (hN : N % 2 = 0) : torusMat N (fun _ => π) = -1 := by
  ext i j
  simp only [torusMat]
  have hi : (i : ℕ) / 2 < N / 2 := by have := i.isLt; omega
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp_all
  · by_cases h : (i : ℕ) / 2 = (j : ℕ) / 2
    · have hpar : (i : ℕ) % 2 ≠ (j : ℕ) % 2 := by
        intro e; exact hij (Fin.ext (by omega))
      split_ifs <;> simp_all
    · simp [h, hij]

/-! ### Determinants of block matrices -/

/-- Laplace expansion along a first column that vanishes below the corner. -/
theorem det_of_col_zero {M : ℕ} (L : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ)
    (h : ∀ a : Fin M, L a.succ 0 = 0) : L.det = L 0 0 * (L.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∑ a : Fin M, (-1 : ℝ) ^ ((a.succ : Fin (M + 1)) : ℕ) * L a.succ 0 *
      (L.submatrix a.succ.succAbove Fin.succ).det = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [h a]; ring
  rw [hz]
  simp

/-- Laplace expansion along the first two columns of a matrix with a `2 × 2` block in the top
left corner and zeros below it. -/
theorem det_of_firstBlock {M : ℕ} (K : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (h0 : ∀ i : Fin M, K i.succ.succ 0 = 0) (h1 : ∀ i : Fin M, K i.succ.succ 1 = 0) :
    K.det = (K 0 0 * K 1 1 - K 0 1 * K 1 0) *
      (K.submatrix (fun i : Fin M => i.succ.succ) (fun j : Fin M => j.succ.succ)).det := by
  set D := (K.submatrix (fun i : Fin M => i.succ.succ) (fun j : Fin M => j.succ.succ)).det
  rw [det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrest : ∑ i : Fin M, (-1 : ℝ) ^ ((i.succ.succ : Fin (M + 2)) : ℕ) * K i.succ.succ 0 *
      (K.submatrix i.succ.succ.succAbove Fin.succ).det = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [h0 i]; ring
  rw [hrest, add_zero]
  have hA : (K.submatrix (Fin.succAbove 0) Fin.succ).det = K 1 1 * D := by
    rw [det_of_col_zero]
    · simp only [submatrix_apply, Fin.succAbove_zero]
      rfl
    · intro a
      simpa [Fin.succAbove_zero] using h1 a
  have hB : (K.submatrix (Fin.succAbove 1) Fin.succ).det = K 0 1 * D := by
    rw [det_of_col_zero]
    · congr 1
    · intro a
      have : (Fin.succAbove (1 : Fin (M + 2)) a.succ) = a.succ.succ := by
        simp [Fin.succAbove, Fin.lt_def]
      simp only [submatrix_apply, this]
      exact h1 a
  have e1 : (Fin.succ (0 : Fin (M + 1)) : Fin (M + 2)) = 1 := rfl
  rw [e1, hA, hB]
  simp
  ring

/-- Laplace expansion along the last column, when it vanishes above the corner and the last row
vanishes to the left of it. -/
theorem det_of_lastBlock {M : ℕ} (K : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ)
    (h : ∀ i : Fin M, K i.castSucc (Fin.last M) = 0) :
    K.det = K (Fin.last M) (Fin.last M) * (K.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_column K (Fin.last M), Fin.sum_univ_castSucc]
  have hz : ∑ i : Fin M, (-1 : ℝ) ^ ((i.castSucc : Fin (M + 1)) + ((Fin.last M : Fin (M + 1)) : ℕ))
      * K i.castSucc (Fin.last M) * (K.submatrix i.castSucc.succAbove (Fin.last M).succAbove).det
      = 0 := Finset.sum_eq_zero fun i _ => by rw [h i]; ring
  rw [hz, zero_add]
  simp only [Fin.succAbove_last, Fin.val_last]
  have : ((-1 : ℝ) ^ (M + M)) = 1 := by rw [← two_mul, pow_mul]; norm_num
  rw [this, one_mul]

/-! ### Orthonormal families of `N` vectors in `ℝᴺ` -/

section Ortho

variable {N : ℕ}

/-- `u 0, …, u (N-1)` is an orthonormal family in `ℝᴺ`. -/
def IsOrthonormalFamily (u : Fin N → Fin N → ℝ) : Prop :=
  ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0

/-- The matrix whose columns are the vectors `u j`. -/
def colMat (u : Fin N → Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => u j i

theorem colMat_transpose_mul {u : Fin N → Fin N → ℝ} (hu : IsOrthonormalFamily u) :
    (colMat u)ᵀ * colMat u = 1 := by
  ext j k
  rw [mul_apply, one_apply, ← hu j k]
  simp [colMat, dotProduct]

theorem colMat_mul_transpose {u : Fin N → Fin N → ℝ} (hu : IsOrthonormalFamily u) :
    colMat u * (colMat u)ᵀ = 1 :=
  mul_eq_one_comm.mp (colMat_transpose_mul hu)

theorem colMat_mulVec_single (u : Fin N → Fin N → ℝ) (j : Fin N) :
    colMat u *ᵥ Pi.single j 1 = u j := by
  ext i
  simp [colMat, mulVec, dotProduct, Pi.single_apply]

theorem colMat_transpose_mulVec (u : Fin N → Fin N → ℝ) (x : Fin N → ℝ) (j : Fin N) :
    ((colMat u)ᵀ *ᵥ x) j = u j ⬝ᵥ x := by
  simp [colMat, mulVec, dotProduct]

/-- Expansion in an orthonormal basis. -/
theorem eq_sum_of_orthonormal {u : Fin N → Fin N → ℝ} (hu : IsOrthonormalFamily u)
    (x : Fin N → ℝ) : x = ∑ j, (u j ⬝ᵥ x) • u j := by
  have h : x = colMat u *ᵥ ((colMat u)ᵀ *ᵥ x) := by
    rw [mulVec_mulVec, colMat_mul_transpose hu, one_mulVec]
  conv_lhs => rw [h]
  ext i
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colMat, of_apply,
    transpose_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Parseval's identity. -/
theorem dotProduct_eq_sum_of_orthonormal {u : Fin N → Fin N → ℝ} (hu : IsOrthonormalFamily u)
    (x y : Fin N → ℝ) : x ⬝ᵥ y = ∑ j, (u j ⬝ᵥ x) * (u j ⬝ᵥ y) := by
  conv_lhs => rw [eq_sum_of_orthonormal hu x]
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_dotProduct, smul_eq_mul]

/-- An orthonormal family with `R u_k = Σ_j t_{jk} u_j` conjugates `R` to `t`. -/
theorem colMat_conj_of_action {u : Fin N → Fin N → ℝ} (hu : IsOrthonormalFamily u)
    {R t : Matrix (Fin N) (Fin N) ℝ} (h : ∀ k, R *ᵥ u k = ∑ j, t j k • u j) :
    (colMat u)ᵀ * R * colMat u = t := by
  ext j k
  have e1 : ((colMat u)ᵀ * R * colMat u) j k = u j ⬝ᵥ (R *ᵥ u k) := by
    simp only [mul_apply, colMat, of_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e1, h k, dotProduct_sum]
  simp_rw [dotProduct_smul, hu j, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

end Ortho

/-! ### Facts about an orthogonal `R` and an eigenvector of `R + Rᵀ` -/

section Eigen

variable {N : ℕ} {R : Matrix (Fin N) (Fin N) ℝ}

theorem dotProduct_mulVec_transpose (x y : Fin N → ℝ) :
    x ⬝ᵥ (R *ᵥ y) = (Rᵀ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose]

theorem mulVec_dotProduct_mulVec (hR : Rᵀ * R = 1) (x y : Fin N → ℝ) :
    (R *ᵥ x) ⬝ᵥ (R *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_comm, dotProduct_mulVec_transpose, mulVec_mulVec, hR, one_mulVec,
    dotProduct_comm]

end Eigen

/-! ### Extending orthonormal families -/

section Extend

theorem inner_toLp_toLp {N : ℕ} (x y : Fin N → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin N)) (WithLp.toLp 2 y) = x ⬝ᵥ y := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem isOrthonormalFamily_of_basis {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    IsOrthonormalFamily fun j => (b j).ofLp := by
  intro j k
  have h := b.orthonormal
  rw [orthonormal_iff_ite] at h
  rw [← h j k]
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem colMat_conj_apply {N : ℕ} (u : Fin N → Fin N → ℝ) (R : Matrix (Fin N) (Fin N) ℝ)
    (j k : Fin N) : ((colMat u)ᵀ * R * colMat u) j k = u j ⬝ᵥ (R *ᵥ u k) := by
  simp only [mul_apply, colMat, of_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem det_colMat_conj {N : ℕ} {u : Fin N → Fin N → ℝ} (hu : IsOrthonormalFamily u)
    (R : Matrix (Fin N) (Fin N) ℝ) : ((colMat u)ᵀ * R * colMat u).det = R.det := by
  have h := congrArg det (colMat_transpose_mul hu)
  rw [det_mul, det_transpose, det_one] at h
  rw [det_mul, det_mul, det_transpose]
  calc (colMat u).det * R.det * (colMat u).det
      = ((colMat u).det * (colMat u).det) * R.det := by ring
    _ = R.det := by rw [h, one_mul]

theorem exists_orthonormal_extension_two {M : ℕ} (v w : Fin (M + 2) → ℝ) (hvv : v ⬝ᵥ v = 1)
    (hww : w ⬝ᵥ w = 1) (hvw : v ⬝ᵥ w = 0) :
    ∃ u : Fin (M + 2) → Fin (M + 2) → ℝ, IsOrthonormalFamily u ∧ u 0 = v ∧ u 1 = w := by
  classical
  let f : Fin (M + 2) → EuclideanSpace ℝ (Fin (M + 2)) := fun i =>
    WithLp.toLp 2 (if i = 0 then v else if i = 1 then w else 0)
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin (M + 2))) = Fintype.card (Fin (M + 2)) := by
    simp
  have h10 : (1 : Fin (M + 2)) ≠ 0 := by simp
  have hon : Orthonormal ℝ (({0, 1} : Set (Fin (M + 2))).domRestrict f) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.domRestrict_apply, f, inner_toLp_toLp]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [hvv, hww, hvw, dotProduct_comm w v, h10, h10.symm]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hon
  refine ⟨fun j => (b j).ofLp, isOrthonormalFamily_of_basis b, ?_, ?_⟩
  · simp [hb 0 (by simp), f]
  · simp [hb 1 (by simp), f, h10]

theorem exists_orthonormal_extension_last {M : ℕ} (v : Fin (M + 1) → ℝ) (hvv : v ⬝ᵥ v = 1) :
    ∃ u : Fin (M + 1) → Fin (M + 1) → ℝ, IsOrthonormalFamily u ∧ u (Fin.last M) = v := by
  classical
  let f : Fin (M + 1) → EuclideanSpace ℝ (Fin (M + 1)) := fun _ => WithLp.toLp 2 v
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin (M + 1))) = Fintype.card (Fin (M + 1)) := by
    simp
  have hon : Orthonormal ℝ (({Fin.last M} : Set (Fin (M + 1))).domRestrict f) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.domRestrict_apply, f, inner_toLp_toLp]
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi hj
    simp [hvv]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hon
  refine ⟨fun j => (b j).ofLp, isOrthonormalFamily_of_basis b, ?_⟩
  simp [hb (Fin.last M) (by simp), f]

end Extend

/-! ### Recombination -/

section Combine

variable {N M : ℕ} {u : Fin N → Fin N → ℝ}

theorem sum_smul_dotProduct_sum_smul (hu : IsOrthonormalFamily u) {e : Fin M → Fin N}
    (he : Function.Injective e) (a b : Fin M → ℝ) :
    (∑ l, a l • u (e l)) ⬝ᵥ (∑ l, b l • u (e l)) = a ⬝ᵥ b := by
  have hu' : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0 := hu
  rw [sum_dotProduct]
  simp_rw [dotProduct_sum, smul_dotProduct, dotProduct_smul, hu', he.eq_iff]
  simp [dotProduct]

theorem sum_smul_dotProduct_of_ne (hu : IsOrthonormalFamily u) (e : Fin M → Fin N) (a : Fin M → ℝ)
    {j : Fin N} (hj : ∀ l, e l ≠ j) : (∑ l, a l • u (e l)) ⬝ᵥ u j = 0 := by
  have hu' : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0 := hu
  rw [sum_dotProduct]
  simp_rw [smul_dotProduct, hu']
  simp [hj]

theorem compose_action {e : Fin M → Fin N} {R : Matrix (Fin N) (Fin N) ℝ}
    {R' t' : Matrix (Fin M) (Fin M) ℝ} (hRu : ∀ k, R *ᵥ u (e k) = ∑ i, R' i k • u (e i))
    {u' : Fin M → Fin M → ℝ} (hact' : ∀ k, R' *ᵥ u' k = ∑ j, t' j k • u' j) (k : Fin M) :
    R *ᵥ (∑ l, u' k l • u (e l)) = ∑ j, t' j k • (∑ l, u' j l • u (e l)) := by
  have key : ∀ i, ∑ l, R' i l * u' k l = ∑ j, t' j k * u' j i := by
    intro i
    have := congrFun (hact' k) i
    simpa [mulVec, dotProduct, Finset.sum_apply] using this
  ext x
  simp only [mulVec_sum, mulVec_smul, hRu, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  calc ∑ l, ∑ i, u' k l * (R' i l * u (e i) x)
      = ∑ i, (∑ l, R' i l * u' k l) * u (e i) x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ i, (∑ j, t' j k * u' j i) * u (e i) x := by simp_rw [key]
    _ = ∑ j, ∑ l, t' j k * (u' j l * u (e l) x) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

end Combine

/-- `t(θ)` only depends on the angles `θ k`, `k < N/2`. -/
theorem torusMat_congr {N : ℕ} {θ θ' : ℕ → ℝ} (h : ∀ k < N / 2, θ k = θ' k) :
    torusMat N θ = torusMat N θ' := by
  ext i j
  simp only [torusMat]
  by_cases h1 : (i : ℕ) / 2 < N / 2 ∧ (i : ℕ) / 2 = (j : ℕ) / 2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1), h _ h1.1]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h1)]

/-! ### The induction -/

/-- The statement proved by induction: an orthonormal basis in which `R` acts as `t(θ)`. -/
def HasTorusForm (N : ℕ) (R : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ (u : Fin N → Fin N → ℝ) (θ : ℕ → ℝ), IsOrthonormalFamily u ∧
    ∀ k, R *ᵥ u k = ∑ j, torusMat N θ j k • u j

/-- **Case of an invariant plane.** -/
theorem hasTorusForm_of_plane {M : ℕ}
    (ih : ∀ R' : Matrix (Fin M) (Fin M) ℝ, R'ᵀ * R' = 1 → R'.det = 1 → HasTorusForm M R')
    {R : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ} (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    {v w : Fin (M + 2) → ℝ} {c σ : ℝ} (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1) (hvw : v ⬝ᵥ w = 0)
    (hcσ : c ^ 2 + σ ^ 2 = 1) (hσ : 0 ≤ σ)
    (hRv : R *ᵥ v = c • v + σ • w) (hRw : R *ᵥ w = (-σ) • v + c • w) :
    HasTorusForm (M + 2) R := by
  -- the transpose acts by the inverse rotation
  have e1 : Rᵀ *ᵥ (R *ᵥ v) = v := by rw [mulVec_mulVec, hR, one_mulVec]
  have e2 : Rᵀ *ᵥ (R *ᵥ w) = w := by rw [mulVec_mulVec, hR, one_mulVec]
  rw [hRv, mulVec_add, mulVec_smul, mulVec_smul] at e1
  rw [hRw, mulVec_add, mulVec_smul, mulVec_smul] at e2
  have hRtv : Rᵀ *ᵥ v = c • v - σ • w := by
    calc Rᵀ *ᵥ v = (c ^ 2 + σ ^ 2) • Rᵀ *ᵥ v := by rw [hcσ, one_smul]
      _ = c • (c • Rᵀ *ᵥ v + σ • Rᵀ *ᵥ w) - σ • ((-σ) • Rᵀ *ᵥ v + c • Rᵀ *ᵥ w) := by module
      _ = c • v - σ • w := by rw [e1, e2]
  have hRtw : Rᵀ *ᵥ w = σ • v + c • w := by
    calc Rᵀ *ᵥ w = (c ^ 2 + σ ^ 2) • Rᵀ *ᵥ w := by rw [hcσ, one_smul]
      _ = σ • (c • Rᵀ *ᵥ v + σ • Rᵀ *ᵥ w) + c • ((-σ) • Rᵀ *ᵥ v + c • Rᵀ *ᵥ w) := by module
      _ = σ • v + c • w := by rw [e1, e2]
  -- an orthonormal basis starting with v, w
  obtain ⟨u, hu, hu0, hu1⟩ := exists_orthonormal_extension_two v w hvv hww hvw
  have hu' : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0 := hu
  have h0s : ∀ k : Fin M, (0 : Fin (M + 2)) ≠ k.succ.succ := fun k => by
    simp [Fin.ext_iff]
  have h1s : ∀ k : Fin M, (1 : Fin (M + 2)) ≠ k.succ.succ := fun k => by
    simp [Fin.ext_iff]
  have hvk : ∀ k : Fin M, v ⬝ᵥ u k.succ.succ = 0 := fun k => by
    rw [← hu0, hu' 0, ite_eq_right_of_eq_false _ _ (eq_false (h0s k))]
  have hwk : ∀ k : Fin M, w ⬝ᵥ u k.succ.succ = 0 := fun k => by
    rw [← hu1, hu' 1, ite_eq_right_of_eq_false _ _ (eq_false (h1s k))]
  have hvR : ∀ k : Fin M, v ⬝ᵥ (R *ᵥ u k.succ.succ) = 0 := fun k => by
    rw [dotProduct_mulVec_transpose, hRtv, sub_dotProduct, smul_dotProduct, smul_dotProduct,
      hvk, hwk]; simp
  have hwR : ∀ k : Fin M, w ⬝ᵥ (R *ᵥ u k.succ.succ) = 0 := fun k => by
    rw [dotProduct_mulVec_transpose, hRtw, add_dotProduct, smul_dotProduct, smul_dotProduct,
      hvk, hwk]; simp
  -- the restriction to the complement
  set R' : Matrix (Fin M) (Fin M) ℝ := Matrix.of fun i j => u i.succ.succ ⬝ᵥ (R *ᵥ u j.succ.succ)
    with hR'
  have hRu : ∀ k : Fin M, R *ᵥ u k.succ.succ = ∑ i, R' i k • u i.succ.succ := by
    intro k
    conv_lhs => rw [eq_sum_of_orthonormal hu (R *ᵥ u k.succ.succ)]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have e0 : u 0 ⬝ᵥ (R *ᵥ u k.succ.succ) = 0 := by rw [hu0]; exact hvR k
    have e1' : u (Fin.succ 0) ⬝ᵥ (R *ᵥ u k.succ.succ) = 0 := by
      rw [show (Fin.succ 0 : Fin (M + 2)) = 1 from rfl, hu1]; exact hwR k
    rw [e0, e1', zero_smul, zero_smul, zero_add, zero_add]
    rfl
  have hR'orth : R'ᵀ * R' = 1 := by
    ext i j
    have h := dotProduct_eq_sum_of_orthonormal hu (R *ᵥ u i.succ.succ) (R *ᵥ u j.succ.succ)
    rw [mulVec_dotProduct_mulVec hR, hu', Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    have e0 : u 0 ⬝ᵥ (R *ᵥ u i.succ.succ) = 0 := by rw [hu0]; exact hvR i
    have e0' : u (Fin.succ 0) ⬝ᵥ (R *ᵥ u i.succ.succ) = 0 := by
      rw [show (Fin.succ 0 : Fin (M + 2)) = 1 from rfl, hu1]; exact hwR i
    rw [e0, e0', zero_mul, zero_mul, zero_add, zero_add] at h
    rw [mul_apply, one_apply]
    simp only [transpose_apply, hR', of_apply]
    rw [← h]
    simp [Fin.ext_iff]
  have hR'det : R'.det = 1 := by
    set K := (colMat u)ᵀ * R * colMat u with hK
    have hKdet : K.det = 1 := by rw [hK, det_colMat_conj hu, hdet]
    have hKe : ∀ j k, K j k = u j ⬝ᵥ (R *ᵥ u k) := colMat_conj_apply u R
    have hK0 : ∀ i : Fin M, K i.succ.succ 0 = 0 := fun i => by
      rw [hKe, hu0, hRv, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm,
        hvk, dotProduct_comm, hwk]; simp
    have hK1 : ∀ i : Fin M, K i.succ.succ 1 = 0 := fun i => by
      rw [hKe, hu1, hRw, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm,
        hvk, dotProduct_comm, hwk]; simp
    have hcorner : K 0 0 * K 1 1 - K 0 1 * K 1 0 = 1 := by
      rw [hKe, hKe, hKe, hKe, hu0, hu1, hRv, hRw]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hvv, hww, hvw, dotProduct_comm w v]
      nlinarith [hcσ]
    have hsub : K.submatrix (fun i : Fin M => i.succ.succ) (fun j : Fin M => j.succ.succ) = R' := by
      ext i j; rw [submatrix_apply, hKe]; rfl
    have := det_of_firstBlock K hK0 hK1
    rw [hKdet, hcorner, one_mul, hsub] at this
    exact this.symm
  obtain ⟨u', θ', hu'', hact'⟩ := ih R' hR'orth hR'det
  -- the new basis and angles
  let U : Fin (M + 2) → Fin (M + 2) → ℝ :=
    Fin.cases v (Fin.cases w fun k => ∑ l, u' k l • u l.succ.succ)
  have hU0 : U 0 = v := rfl
  have hU1 : U 1 = w := rfl
  have hUs : ∀ k : Fin M, U k.succ.succ = ∑ l, u' k l • u l.succ.succ := fun _ => rfl
  have hc1 : -1 ≤ c ∧ c ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg σ, sq_nonneg (c + 1), sq_nonneg (c - 1)]
  set θ : ℕ → ℝ := fun i => if i = 0 then Real.arccos c else θ' (i - 1) with hθ
  have hcos : cos (θ 0) = c := by simp [hθ, Real.cos_arccos hc1.1 hc1.2]
  have hsin : sin (θ 0) = σ := by
    simp only [hθ, ite_true, Real.sin_arccos]
    rw [show 1 - c ^ 2 = σ ^ 2 by linarith, Real.sqrt_sq hσ]
  have hθs : (fun k => θ (k + 1)) = θ' := by funext k; simp [hθ]
  refine ⟨U, θ, ?_, ?_⟩
  · -- orthonormality
    have he : Function.Injective (fun l : Fin M => (l.succ.succ : Fin (M + 2))) :=
      fun a b h => Fin.succ_injective _ (Fin.succ_injective _ h)
    have hsv : ∀ k : Fin M, (∑ l, u' k l • u l.succ.succ) ⬝ᵥ v = 0 := fun k => by
      rw [← hu0]; exact sum_smul_dotProduct_of_ne hu _ _ (fun l => (h0s l).symm)
    have hsw : ∀ k : Fin M, (∑ l, u' k l • u l.succ.succ) ⬝ᵥ w = 0 := fun k => by
      rw [← hu1]; exact sum_smul_dotProduct_of_ne hu _ _ (fun l => (h1s l).symm)
    have hU1' : U (Fin.succ 0) = w := rfl
    have hvw' : w ⬝ᵥ v = 0 := by rw [dotProduct_comm, hvw]
    intro J K
    refine Fin.cases ?_ (fun J => Fin.cases ?_ (fun j => ?_) J) J <;>
      refine Fin.cases ?_ (fun K => Fin.cases ?_ (fun k => ?_) K) K
    · rw [hU0]; simp [hvv]
    · rw [hU0, hU1', hvw]; simp
    · rw [hU0, hUs, dotProduct_comm, hsv]; simp [Fin.ext_iff]
    · rw [hU1', hU0, hvw']; simp
    · rw [hU1']; simp [hww]
    · rw [hU1', hUs, dotProduct_comm, hsw]; simp [Fin.ext_iff]
    · rw [hUs, hU0, hsv]; simp [Fin.ext_iff]
    · rw [hUs, hU1', hsw]; simp [Fin.ext_iff]
    · rw [hUs, hUs, sum_smul_dotProduct_sum_smul hu he, hu'' j k]
      simp [Fin.ext_iff]
  · -- the action
    intro K
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun K => Fin.cases ?_ (fun k => ?_) K) K
    · simp only [show (Fin.succ 0 : Fin (M + 2)) = 1 from rfl, torusMat_zero_zero,
        torusMat_one_zero, torusMat_succ_succ_zero, zero_smul, Finset.sum_const_zero, add_zero,
        hcos, hsin]
      exact hRv
    · simp only [show (Fin.succ 0 : Fin (M + 2)) = 1 from rfl, torusMat_zero_one,
        torusMat_one_one, torusMat_succ_succ_one, zero_smul, Finset.sum_const_zero, add_zero,
        hcos, hsin]
      exact hRw
    · simp only [show (Fin.succ 0 : Fin (M + 2)) = 1 from rfl, torusMat_zero_succ_succ,
        torusMat_one_succ_succ, torusMat_succ_succ, zero_smul, zero_add, hθs]
      exact compose_action (e := fun l : Fin M => (l.succ.succ : Fin (M + 2))) hRu hact' k

/-- **Case of a fixed vector.** -/
theorem hasTorusForm_of_fixed {M : ℕ}
    (ih : ∀ R' : Matrix (Fin M) (Fin M) ℝ, R'ᵀ * R' = 1 → R'.det = 1 → HasTorusForm M R')
    {R : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ} (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    {v : Fin (M + 1) → ℝ} (hvv : v ⬝ᵥ v = 1) (hRv : R *ᵥ v = v) :
    HasTorusForm (M + 1) R := by
  have hRtv : Rᵀ *ᵥ v = v := by
    calc Rᵀ *ᵥ v = Rᵀ *ᵥ (R *ᵥ v) := by rw [hRv]
      _ = v := by rw [mulVec_mulVec, hR, one_mulVec]
  obtain ⟨u, hu, hul⟩ := exists_orthonormal_extension_last v hvv
  have hu' : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0 := hu
  have hls : ∀ k : Fin M, Fin.last M ≠ k.castSucc := fun k => (Fin.castSucc_lt_last k).ne'
  have hvk : ∀ k : Fin M, v ⬝ᵥ u k.castSucc = 0 := fun k => by
    rw [← hul, hu', ite_eq_right_of_eq_false _ _ (eq_false (hls k))]
  have hvR : ∀ k : Fin M, v ⬝ᵥ (R *ᵥ u k.castSucc) = 0 := fun k => by
    rw [dotProduct_mulVec_transpose, hRtv, hvk]
  set R' : Matrix (Fin M) (Fin M) ℝ := Matrix.of fun i j => u i.castSucc ⬝ᵥ (R *ᵥ u j.castSucc)
    with hR'
  have hRu : ∀ k : Fin M, R *ᵥ u k.castSucc = ∑ i, R' i k • u i.castSucc := by
    intro k
    conv_lhs => rw [eq_sum_of_orthonormal hu (R *ᵥ u k.castSucc)]
    rw [Fin.sum_univ_castSucc, hul, hvR k, zero_smul, add_zero]
    rfl
  have hR'orth : R'ᵀ * R' = 1 := by
    ext i j
    have h := dotProduct_eq_sum_of_orthonormal hu (R *ᵥ u i.castSucc) (R *ᵥ u j.castSucc)
    rw [mulVec_dotProduct_mulVec hR, hu', Fin.sum_univ_castSucc, hul, hvR i, zero_mul,
      add_zero] at h
    rw [mul_apply, one_apply]
    simp only [transpose_apply, hR', of_apply]
    rw [← h]
    simp [Fin.ext_iff]
  have hR'det : R'.det = 1 := by
    set K := (colMat u)ᵀ * R * colMat u with hK
    have hKdet : K.det = 1 := by rw [hK, det_colMat_conj hu, hdet]
    have hKe : ∀ j k, K j k = u j ⬝ᵥ (R *ᵥ u k) := colMat_conj_apply u R
    have hKl : ∀ i : Fin M, K i.castSucc (Fin.last M) = 0 := fun i => by
      rw [hKe, hul, hRv, dotProduct_comm, hvk]
    have hcorner : K (Fin.last M) (Fin.last M) = 1 := by rw [hKe, hul, hRv, hvv]
    have hsub : K.submatrix Fin.castSucc Fin.castSucc = R' := by
      ext i j; rw [submatrix_apply, hKe]; rfl
    have := det_of_lastBlock K hKl
    rw [hKdet, hcorner, one_mul, hsub] at this
    exact this.symm
  obtain ⟨u', θ', hu'', hact'⟩ := ih R' hR'orth hR'det
  let U : Fin (M + 1) → Fin (M + 1) → ℝ :=
    Fin.lastCases v fun k => ∑ l, u' k l • u l.castSucc
  have hUl : U (Fin.last M) = v := by simp [U]
  have hUc : ∀ k : Fin M, U k.castSucc = ∑ l, u' k l • u l.castSucc := fun k => by simp [U]
  set θ : ℕ → ℝ := Function.update θ' (M / 2) 0 with hθ
  have hθM : M % 2 = 1 → θ (M / 2) = 0 := fun _ => by simp [hθ]
  have hθ' : torusMat M θ = torusMat M θ' := torusMat_congr fun k hk => by
    simp [hθ, hk.ne]
  refine ⟨U, θ, ?_, ?_⟩
  · have he : Function.Injective (fun l : Fin M => (l.castSucc : Fin (M + 1))) :=
      Fin.castSucc_injective M
    have hsv : ∀ k : Fin M, (∑ l, u' k l • u l.castSucc) ⬝ᵥ v = 0 := fun k => by
      rw [← hul]; exact sum_smul_dotProduct_of_ne hu _ _ (fun l => (hls l).symm)
    intro J K
    refine Fin.lastCases ?_ (fun j => ?_) J <;> refine Fin.lastCases ?_ (fun k => ?_) K
    · rw [hUl]; simp [hvv]
    · rw [hUl, hUc, dotProduct_comm, hsv]; simp [hls k]
    · rw [hUc, hUl, hsv]; simp [(hls j).symm]
    · rw [hUc, hUc, sum_smul_dotProduct_sum_smul hu he, hu'' j k]
      simp [Fin.ext_iff]
  · intro K
    rw [Fin.sum_univ_castSucc]
    refine Fin.lastCases ?_ (fun k => ?_) K
    · simp only [torusMat_castSucc_last θ hθM, torusMat_last_last θ hθM, zero_smul,
        Finset.sum_const_zero, zero_add, one_smul, hUl]
      exact hRv
    · simp only [torusMat_castSucc θ hθM, torusMat_last_castSucc θ hθM, zero_smul, add_zero,
        hθ', hUc]
      exact compose_action (e := fun l : Fin M => (l.castSucc : Fin (M + 1))) hRu hact' k

/-- **Case `R = -1`** (necessarily in even dimension). -/
theorem hasTorusForm_neg_one {N : ℕ} (hN : N % 2 = 0) : HasTorusForm N (-1) := by
  classical
  refine ⟨fun k => Pi.single k 1, fun _ => π, ?_, ?_⟩
  · intro j k
    by_cases h : j = k
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro k
    rw [torusMat_pi hN]
    ext i
    simp [Finset.sum_apply, one_apply, ite_apply, Pi.single_apply]

theorem dotProduct_self_nonneg' {N : ℕ} (x : Fin N → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- **The normal form, as an orthonormal basis.** -/
theorem hasTorusForm (N : ℕ) :
    ∀ R : Matrix (Fin N) (Fin N) ℝ, Rᵀ * R = 1 → R.det = 1 → HasTorusForm N R := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro R hR hdet
  have hRt : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  set S := R + Rᵀ with hSdef
  have hS : S.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hSdef, transpose_add,
      transpose_transpose, add_comm]
  set e : Fin N → Fin N → ℝ := fun j => (hS.eigenvectorBasis j).ofLp with he_def
  have he : IsOrthonormalFamily e := isOrthonormalFamily_of_basis _
  have hSe : ∀ j, S *ᵥ e j = hS.eigenvalues j • e j := hS.mulVec_eigenvectorBasis
  have hvv_of : ∀ j, e j ⬝ᵥ e j = 1 := fun j => by simpa using he j j
  have hRx : ∀ x : Fin N → ℝ, x ⬝ᵥ (S *ᵥ x) = 2 * (x ⬝ᵥ (R *ᵥ x)) := by
    intro x
    have h : x ⬝ᵥ (Rᵀ *ᵥ x) = x ⬝ᵥ (R *ᵥ x) := by
      rw [dotProduct_mulVec_transpose (R := Rᵀ), transpose_transpose, dotProduct_comm]
    rw [hSdef, add_mulVec, dotProduct_add, h]
    ring
  have hRR : ∀ x : Fin N → ℝ, (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ x := fun x =>
    mulVec_dotProduct_mulVec hR x x
  -- facts about a unit eigenvector `v` with eigenvalue `s`
  have hdot : ∀ (v : Fin N → ℝ) (s : ℝ), v ⬝ᵥ v = 1 → S *ᵥ v = s • v →
      v ⬝ᵥ (R *ᵥ v) = s / 2 := by
    intro v s hvv hSv
    have := hRx v
    rw [hSv, dotProduct_smul, hvv, smul_eq_mul, mul_one] at this
    linarith
  have hsq : ∀ (v : Fin N → ℝ) (s : ℝ), S *ᵥ v = s • v →
      R *ᵥ (R *ᵥ v) = s • (R *ᵥ v) - v := by
    intro v s hSv
    have h1 : R *ᵥ (S *ᵥ v) = R *ᵥ (R *ᵥ v) + v := by
      rw [hSdef, add_mulVec, mulVec_add,
        show R *ᵥ (Rᵀ *ᵥ v) = v by rw [mulVec_mulVec, hRt, one_mulVec]]
    rw [hSv, mulVec_smul] at h1
    rw [h1]; abel
  have hbound : ∀ (v : Fin N → ℝ) (s : ℝ), v ⬝ᵥ v = 1 → S *ᵥ v = s • v → -2 ≤ s ∧ s ≤ 2 := by
    intro v s hvv hSv
    have h1 := dotProduct_self_nonneg' (R *ᵥ v - v)
    have h2 := dotProduct_self_nonneg' (R *ᵥ v + v)
    have hd := hdot v s hvv hSv
    have hd' : (R *ᵥ v) ⬝ᵥ v = s / 2 := by rw [dotProduct_comm, hd]
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add, hRR, hvv,
      hd, hd'] at h1 h2
    constructor <;> linarith
  by_cases hA : ∃ j, hS.eigenvalues j ≠ 2 ∧ hS.eigenvalues j ≠ -2
  · -- an invariant plane
    obtain ⟨j, hj2, hjm2⟩ := hA
    set v := e j with hv
    set s := hS.eigenvalues j with hs
    have hvv : v ⬝ᵥ v = 1 := hvv_of j
    have hd := hdot v s hvv (hSe j)
    have hRRv := hsq v s (hSe j)
    obtain ⟨hs1, hs2⟩ := hbound v s hvv (hSe j)
    set c := s / 2 with hc
    have hc1 : c ^ 2 < 1 := by
      have h1 : -2 < s := lt_of_le_of_ne hs1 (Ne.symm hjm2)
      have h2 : s < 2 := lt_of_le_of_ne hs2 hj2
      nlinarith
    set σ := Real.sqrt (1 - c ^ 2) with hσ
    have hσpos : 0 < σ := Real.sqrt_pos.mpr (by linarith)
    have hσsq : σ ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by linarith)
    have hcσ : c ^ 2 + σ ^ 2 = 1 := by linarith
    set w := σ⁻¹ • (R *ᵥ v - c • v) with hw
    have hσw : σ • w = R *ᵥ v - c • v := by
      rw [hw, smul_smul, mul_inv_cancel₀ hσpos.ne', one_smul]
    have hRv : R *ᵥ v = c • v + σ • w := by rw [hσw]; abel
    have hd' : (R *ᵥ v) ⬝ᵥ v = s / 2 := by rw [dotProduct_comm, hd]
    have hww : w ⬝ᵥ w = 1 := by
      have h : (σ • w) ⬝ᵥ (σ • w) = σ ^ 2 := by
        rw [hσw]
        simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, hRR, hvv,
          hd, hd', smul_eq_mul]
        rw [hσsq, hc]; ring
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
      have : σ * σ ≠ 0 := by positivity
      field_simp at h
      nlinarith [h]
    have hvw : v ⬝ᵥ w = 0 := by
      have h : v ⬝ᵥ (σ • w) = 0 := by
        rw [hσw, dotProduct_sub, dotProduct_smul, hd, hvv, hc]; simp
      rw [dotProduct_smul, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_left hσpos.ne'
    have hRw : R *ᵥ w = (-σ) • v + c • w := by
      have hs2c : s = 2 * c := by rw [hc]; ring
      have hL : σ • (R *ᵥ w) = c • (R *ᵥ v) - v := by
        rw [← mulVec_smul, hσw, mulVec_sub, mulVec_smul, hRRv, hs2c]
        module
      have hRside : σ • ((-σ) • v + c • w) = c • (R *ᵥ v) - v := by
        rw [smul_add, smul_smul, smul_comm σ c w, hσw,
          show σ * -σ = -(1 - c ^ 2) by nlinarith [hσsq]]
        module
      exact smul_right_injective _ hσpos.ne' (hL.trans hRside.symm)
    -- the dimension is at least two
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := by
      rcases N with _ | _ | M
      · simp [dotProduct] at hvv
      · exfalso
        simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hvv hww hvw
        nlinarith [hvv, hww, hvw]
      · exact ⟨M, rfl⟩
    exact hasTorusForm_of_plane (ih M (by omega)) hR hdet hvv hww hvw hcσ hσpos.le hRv hRw
  · push Not at hA
    by_cases hB : ∃ j, hS.eigenvalues j = 2
    · -- a fixed vector
      obtain ⟨j, hj⟩ := hB
      set v := e j with hv
      have hvv : v ⬝ᵥ v = 1 := hvv_of j
      have hd := hdot v (hS.eigenvalues j) hvv (hSe j)
      rw [hj] at hd
      have hRv : R *ᵥ v = v := by
        have h := dotProduct_self_nonneg' (R *ᵥ v - v)
        have hd' : (R *ᵥ v) ⬝ᵥ v = 2 / 2 := by rw [dotProduct_comm, hd]
        have h0 : (R *ᵥ v - v) ⬝ᵥ (R *ᵥ v - v) = 0 := by
          simp only [sub_dotProduct, dotProduct_sub, hRR, hvv, hd, hd']
          ring
        exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h0)
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := by
        rcases N with _ | M
        · simp [dotProduct] at hvv
        · exact ⟨M, rfl⟩
      exact hasTorusForm_of_fixed (ih M (by omega)) hR hdet hvv hRv
    · -- `R = -1`
      push Not at hB
      have hall : ∀ j, hS.eigenvalues j = -2 := fun j => hA j (hB j)
      have hSx : ∀ x : Fin N → ℝ, S *ᵥ x = (-2 : ℝ) • x := by
        intro x
        conv_lhs => rw [eq_sum_of_orthonormal he x]
        rw [mulVec_sum]
        simp_rw [mulVec_smul, hSe, hall, smul_comm _ (-2 : ℝ)]
        rw [← Finset.smul_sum, ← eq_sum_of_orthonormal he x]
      have hRneg : R = -1 := by
        have hcol : ∀ x : Fin N → ℝ, R *ᵥ x = -x := by
          intro x
          have h0 : (R *ᵥ x + x) ⬝ᵥ (R *ᵥ x + x) = 0 := by
            have := hRx x
            rw [hSx, dotProduct_smul, smul_eq_mul] at this
            have hc' : (R *ᵥ x) ⬝ᵥ x = x ⬝ᵥ (R *ᵥ x) := dotProduct_comm _ _
            simp only [add_dotProduct, dotProduct_add, hRR, hc']
            linarith
          exact eq_neg_of_add_eq_zero_left (dotProduct_self_eq_zero.mp h0)
        ext i k
        have := congrFun (hcol (Pi.single k 1)) i
        simpa [Matrix.mulVec_single, Pi.single_apply, one_apply] using this
      have hN : N % 2 = 0 := by
        rw [hRneg, det_neg, det_one, Fintype.card_fin, mul_one] at hdet
        rcases Nat.even_or_odd N with h | h
        · exact Nat.even_iff.mp h
        · rw [h.neg_one_pow] at hdet; norm_num at hdet
      rw [hRneg]
      exact hasTorusForm_neg_one hN

/-- The diagonal reflection in the first coordinate. -/
def flip0 (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := diagonal fun i => if (i : ℕ) = 0 then -1 else 1

theorem flip0_mul_flip0 (N : ℕ) : flip0 N * flip0 N = 1 := by
  rw [flip0, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; split_ifs <;> norm_num

/-- Conjugating `t(θ)` by the reflection in the first coordinate negates the first angle. -/
theorem flip0_torusMat_flip0 (N : ℕ) (θ : ℕ → ℝ) :
    flip0 N * torusMat N θ * flip0 N = torusMat N (Function.update θ 0 (-θ 0)) := by
  ext i j
  simp only [flip0, diagonal_mul, mul_diagonal]
  rcases N with _ | _ | M
  · exact i.elim0
  · -- `N = 1`: there are no planes
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [torusMat]
  · have hs : (fun k => Function.update θ 0 (-θ 0) (k + 1)) = fun k => θ (k + 1) := by
      funext k; simp
    have hss : ∀ k : Fin M, ((k.succ.succ : Fin (M + 2)) : ℕ) ≠ 0 := fun k => by simp
    have h1 : ((1 : Fin (M + 2)) : ℕ) ≠ 0 := by simp
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
      simp only [show (Fin.succ 0 : Fin (M + 2)) = 1 from rfl, Fin.val_zero, h1, hss,
        ite_true, ite_false, torusMat_zero_zero, torusMat_zero_one, torusMat_one_zero,
        torusMat_one_one, torusMat_zero_succ_succ, torusMat_one_succ_succ,
        torusMat_succ_succ_zero, torusMat_succ_succ_one, torusMat_succ_succ, hs,
        Function.update_self, cos_neg, sin_neg] <;> ring

/-- **Normal form of a rotation.** Every `R ∈ SO(N)` is `P t(θ) Pᵀ` for some `P ∈ SO(N)`. -/
theorem exists_torusMat_conj {N : ℕ} {R : Matrix (Fin N) (Fin N) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin N) ℝ) :
    ∃ P ∈ specialOrthogonalGroup (Fin N) ℝ, ∃ θ : ℕ → ℝ, R = P * torusMat N θ * Pᵀ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff'] at hR
  obtain ⟨hRo, hdet⟩ := hR
  have hRt : Rᵀ * R = 1 := by simpa [star_eq_conjTranspose] using hRo
  obtain ⟨u, θ, hu, hact⟩ := hasTorusForm N R hRt hdet
  set P₀ := colMat u
  have hP₀ : P₀ᵀ * P₀ = 1 := colMat_transpose_mul hu
  have hP₀' : P₀ * P₀ᵀ = 1 := colMat_mul_transpose hu
  have hconj : P₀ᵀ * R * P₀ = torusMat N θ := colMat_conj_of_action hu hact
  have hR_eq : R = P₀ * torusMat N θ * P₀ᵀ := by
    rw [← hconj]
    calc R = (P₀ * P₀ᵀ) * R * (P₀ * P₀ᵀ) := by rw [hP₀', Matrix.one_mul, Matrix.mul_one]
      _ = P₀ * (P₀ᵀ * R * P₀) * P₀ᵀ := by simp only [Matrix.mul_assoc]
  have hdet₀ : P₀.det * P₀.det = 1 := by
    have := congrArg det hP₀
    rwa [det_mul, det_transpose, det_one] at this
  have hmem : ∀ P : Matrix (Fin N) (Fin N) ℝ, Pᵀ * P = 1 → P.det = 1 →
      P ∈ specialOrthogonalGroup (Fin N) ℝ := fun P h1 h2 => by
    rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff']
    exact ⟨by simpa [star_eq_conjTranspose] using h1, h2⟩
  by_cases hd : P₀.det = 1
  · exact ⟨P₀, hmem P₀ hP₀ hd, θ, hR_eq⟩
  · -- flip the first column
    have hd' : P₀.det = -1 := by
      have : (P₀.det - 1) * (P₀.det + 1) = 0 := by linear_combination hdet₀
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linarith) hd
      · linarith
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; exact absurd (by simp) hd
    have hflipT : (flip0 N)ᵀ = flip0 N := by simp [flip0]
    have hflipdet : (flip0 N).det = -1 := by
      rw [flip0, det_diagonal]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Fin.prod_univ_succ]
      simp
    refine ⟨P₀ * flip0 N, hmem _ ?_ ?_, Function.update θ 0 (-θ 0), ?_⟩
    · rw [transpose_mul, hflipT, Matrix.mul_assoc, ← Matrix.mul_assoc P₀ᵀ, hP₀, Matrix.one_mul,
        flip0_mul_flip0]
    · rw [det_mul, hd', hflipdet]; norm_num
    · rw [← flip0_torusMat_flip0, transpose_mul, hflipT]
      calc R = P₀ * torusMat N θ * P₀ᵀ := hR_eq
        _ = P₀ * (flip0 N * flip0 N) * torusMat N θ * (flip0 N * flip0 N) * P₀ᵀ := by
          rw [flip0_mul_flip0, Matrix.mul_one, Matrix.mul_one]
        _ = P₀ * flip0 N * (flip0 N * torusMat N θ * flip0 N) * (flip0 N * P₀ᵀ) := by
          simp only [Matrix.mul_assoc]

end SOnMCMC

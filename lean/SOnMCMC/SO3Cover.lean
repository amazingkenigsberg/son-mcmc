import SOnMCMC.SO2
import SOnMCMC.SU2Gap

/-!
# The double cover `SU(2) → SO(3)`

Paper: Section 6.5.

* `quatRot w x y z`: the rotation matrix of the quaternion `w + x i + y j + z k`;
* `cover : SU(2) →* SO(3)`: the covering homomorphism, `continuous_cover`;
* `cover_surjective`: every rotation is covered (by an Euler-angle decomposition
  `R = R_x R_y R_x`, each factor being the image of an explicit element of `SU(2)`);
* `trace_covMat`: `tr (cover q) = 4 (Re q₀₀)² - 1`;
* `one_le_of_posSemidef_symPart`: if the symmetric part of `cover q` is positive semidefinite
  then `(Re q₀₀)² ≥ 1/2`.
-/

open Matrix Real
open scoped ComplexConjugate

noncomputable section

namespace SOnMCMC

/-! ### The quaternion rotation matrix -/

/-- The rotation matrix of the quaternion `w + x i + y j + z k`. -/
def quatRot (w x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2, 2 * (x * y - w * z), 2 * (x * z + w * y);
     2 * (x * y + w * z), w ^ 2 - x ^ 2 + y ^ 2 - z ^ 2, 2 * (y * z - w * x);
     2 * (x * z - w * y), 2 * (y * z + w * x), w ^ 2 - x ^ 2 - y ^ 2 + z ^ 2]

/-- `quatRot` is multiplicative for the quaternion product. -/
theorem quatRot_mul (w x y z w' x' y' z' : ℝ) :
    quatRot w x y z * quatRot w' x' y' z'
      = quatRot (w * w' - x * x' - y * y' - z * z') (w * x' + x * w' + y * z' - z * y')
          (w * y' - x * z' + y * w' + z * x') (w * z' + x * y' - y * x' + z * w') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatRot, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem quatRot_mul_transpose (w x y z : ℝ) :
    quatRot w x y z * (quatRot w x y z)ᵀ
      = ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatRot, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_quatRot (w x y z : ℝ) :
    (quatRot w x y z).det = (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) ^ 3 := by
  simp only [quatRot, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
  simp
  ring

/-! ### The covering homomorphism -/

/-- The rotation of `ℝ³` associated with `q ∈ SU(2)`. -/
def covMat (q : SU2) : Matrix (Fin 3) (Fin 3) ℝ :=
  quatRot (q.1 0 0).re (q.1 0 0).im (q.1 0 1).re (q.1 0 1).im

theorem su2_norm_eq (q : SU2) :
    (q.1 0 0).re ^ 2 + (q.1 0 0).im ^ 2 + (q.1 0 1).re ^ 2 + (q.1 0 1).im ^ 2 = 1 := by
  have h := SU2.normSq_add q
  rw [Complex.mul_conj, Complex.mul_conj] at h
  have h' : Complex.normSq (q.1 0 0) + Complex.normSq (q.1 0 1) = 1 := by exact_mod_cast h
  rw [Complex.normSq_apply, Complex.normSq_apply] at h'
  linear_combination h'

theorem covMat_mul (p q : SU2) : covMat (p * q) = covMat p * covMat q := by
  have h00 : (p * q : SU2).1 0 0 = p.1 0 0 * q.1 0 0 - p.1 0 1 * conj (q.1 0 1) := by
    rw [SU2.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, SU2.coe_10 q]
    ring
  have h01 : (p * q : SU2).1 0 1 = p.1 0 0 * q.1 0 1 + p.1 0 1 * conj (q.1 0 0) := by
    rw [SU2.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, SU2.coe_11 q]
  rw [covMat, covMat, covMat, quatRot_mul, h00, h01]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  congr 1 <;> ring

theorem covMat_mem (q : SU2) : covMat q ∈ specialOrthogonalGroup (Fin 3) ℝ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  constructor
  · rw [covMat, quatRot_mul_transpose, su2_norm_eq, one_pow, one_smul]
  · rw [covMat, det_quatRot, su2_norm_eq, one_pow]

theorem covMat_one : covMat 1 = 1 := by
  rw [covMat, SU2.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatRot]

/-- **The covering homomorphism `SU(2) → SO(3)`.** -/
def cover : SU2 →* SO 3 where
  toFun q := ⟨covMat q, covMat_mem q⟩
  map_one' := Subtype.ext covMat_one
  map_mul' p q := Subtype.ext (covMat_mul p q)

@[simp] theorem coe_cover (q : SU2) : ((cover q : SO 3) : Matrix (Fin 3) (Fin 3) ℝ) = covMat q :=
  rfl

theorem continuous_covMat : Continuous covMat := by
  have hq : Continuous fun p : ℝ × ℝ × ℝ × ℝ => quatRot p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [quatRot] <;> fun_prop
  have h00 := continuous_coord 0 0
  have h01 := continuous_coord 0 1
  have hc : Continuous fun q : SU2 =>
      ((q.1 0 0).re, (q.1 0 0).im, (q.1 0 1).re, (q.1 0 1).im) :=
    (Complex.continuous_re.comp h00).prodMk ((Complex.continuous_im.comp h00).prodMk
      ((Complex.continuous_re.comp h01).prodMk (Complex.continuous_im.comp h01)))
  have e : covMat = (fun p : ℝ × ℝ × ℝ × ℝ => quatRot p.1 p.2.1 p.2.2.1 p.2.2.2)
      ∘ fun q : SU2 => ((q.1 0 0).re, (q.1 0 0).im, (q.1 0 1).re, (q.1 0 1).im) := rfl
  rw [e]
  exact hq.comp hc

theorem continuous_cover : Continuous cover := Continuous.subtype_mk continuous_covMat _

/-- `cover (-q) = cover q`. -/
theorem cover_negOne_mul (q : SU2) : cover (negOne * q) = cover q := by
  have h : cover negOne = 1 := by
    apply Subtype.ext
    show covMat negOne = 1
    rw [covMat, negOne, SU2.mk'_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quatRot]
  rw [map_mul, h, one_mul]

/-! ### Rotations about the coordinate axes -/

/-- The rotation about the first axis. -/
def rotX (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, cos t, -sin t; 0, sin t, cos t]

/-- The rotation about the second axis. -/
def rotY (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![cos s, 0, sin s; 0, 1, 0; -sin s, 0, cos s]

theorem covMat_torus (φ : ℝ) : covMat (torus φ) = rotX (2 * φ) := by
  have h00 : (torus φ).1 0 0 = Complex.exp (φ * Complex.I) := by
    rw [torus_coe]
    rfl
  have h01 : (torus φ).1 0 1 = 0 := by
    rw [torus_coe]
    rfl
  rw [covMat, h00, h01, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.zero_re, Complex.zero_im, quatRot, rotX, cos_two_mul, sin_two_mul]
  have h := sin_sq_add_cos_sq φ
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- The element of `SU(2)` covering a rotation about the second axis. -/
def yEl (β : ℝ) : SU2 := SU2.mk' ((cos β : ℝ) : ℂ) ((sin β : ℝ) : ℂ) (by
  rw [Complex.conj_ofReal, Complex.conj_ofReal]
  have h := cos_sq_add_sin_sq β
  have h' : cos β * cos β + sin β * sin β = 1 := by nlinarith
  exact_mod_cast h')

theorem covMat_yEl (β : ℝ) : covMat (yEl β) = rotY (2 * β) := by
  have h00 : (yEl β).1 0 0 = ((cos β : ℝ) : ℂ) := rfl
  have h01 : (yEl β).1 0 1 = ((sin β : ℝ) : ℂ) := rfl
  rw [covMat, h00, h01, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.ofReal_im, quatRot, rotY, cos_two_mul, sin_two_mul]
  have h := sin_sq_add_cos_sq β
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-! ### Surjectivity -/

theorem exists_cos_sin {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) : ∃ t : ℝ, cos t = u ∧ sin t = v := by
  have hM : !![u, -v; v, u] ∈ specialOrthogonalGroup (Fin 2) ℝ := by
    rw [of_mem_specialOrthogonalGroup_fin_two_iff]
    exact ⟨rfl, rfl, by rw [neg_sq]; exact h⟩
  obtain ⟨t, ht⟩ := exists_rotMat_eq hM
  refine ⟨t, ?_, ?_⟩
  · have := congrFun (congrFun ht 0) 0
    simpa [rotMat] using this
  · have := congrFun (congrFun ht 1) 0
    simpa [rotMat] using this

theorem exists_angle_elim (b c : ℝ) : ∃ t : ℝ, cos t * b - sin t * c = 0 := by
  by_cases h : b ^ 2 + c ^ 2 = 0
  · have hb2 : b ^ 2 = 0 := by linarith [sq_nonneg b, sq_nonneg c]
    have hc2 : c ^ 2 = 0 := by linarith [sq_nonneg b, sq_nonneg c]
    have hb : b = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hb2
    have hc : c = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hc2
    exact ⟨0, by simp [hb, hc]⟩
  · have hpos : 0 < b ^ 2 + c ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = √(b ^ 2 + c ^ 2) := ⟨_, rfl⟩
    have hρpos : 0 < ρ := by
      rw [hρ]
      exact Real.sqrt_pos.mpr hpos
    have hρ2 : ρ ^ 2 = b ^ 2 + c ^ 2 := by
      rw [hρ]
      exact Real.sq_sqrt hpos.le
    obtain ⟨t, hc', hs'⟩ := exists_cos_sin (u := c / ρ) (v := b / ρ) (by
      field_simp
      linarith)
    refine ⟨t, ?_⟩
    rw [hc', hs']
    ring

/-- A rotation of `ℝ³` fixing the first basis vector is a rotation about the first axis. -/
theorem eq_rotX_of_entry {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 3) ℝ) (h00 : M 0 0 = 1) : ∃ ψ : ℝ, M = rotX ψ := by
  obtain ⟨horth, hdet⟩ := mem_specialOrthogonalGroup_iff.mp hM
  have h1 : M * Mᵀ = 1 := (mem_orthogonalGroup_iff (Fin 3) ℝ).mp horth
  have h2 : Mᵀ * M = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp horth
  have r0 := congrFun (congrFun h1 0) 0
  have c0 := congrFun (congrFun h2 0) 0
  have r1 := congrFun (congrFun h1 1) 1
  have r2 := congrFun (congrFun h1 2) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq]
    at r0 c0 r1 r2
  rw [h00] at r0 c0
  have e01 : M 0 1 = 0 := by
    have : M 0 1 ^ 2 = 0 := by nlinarith [sq_nonneg (M 0 1), sq_nonneg (M 0 2)]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have e02 : M 0 2 = 0 := by
    have : M 0 2 ^ 2 = 0 := by nlinarith [sq_nonneg (M 0 1), sq_nonneg (M 0 2)]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have e10 : M 1 0 = 0 := by
    have : M 1 0 ^ 2 = 0 := by nlinarith [sq_nonneg (M 1 0), sq_nonneg (M 2 0)]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have e20 : M 2 0 = 0 := by
    have : M 2 0 ^ 2 = 0 := by nlinarith [sq_nonneg (M 1 0), sq_nonneg (M 2 0)]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  rw [Matrix.det_fin_three, h00, e01, e02, e10, e20] at hdet
  rw [e10] at r1
  rw [e20] at r2
  have hB : !![M 1 1, M 1 2; M 2 1, M 2 2] ∈ specialOrthogonalGroup (Fin 2) ℝ := by
    rw [of_mem_specialOrthogonalGroup_fin_two_iff]
    have hsq : (M 1 1 - M 2 2) ^ 2 + (M 1 2 + M 2 1) ^ 2 = 0 := by
      linear_combination r1 + r2 - 2 * hdet
    have ha : (M 1 1 - M 2 2) ^ 2 = 0 := by
      linarith [sq_nonneg (M 1 1 - M 2 2), sq_nonneg (M 1 2 + M 2 1)]
    have hb : (M 1 2 + M 2 1) ^ 2 = 0 := by
      linarith [sq_nonneg (M 1 1 - M 2 2), sq_nonneg (M 1 2 + M 2 1)]
    have ha' := pow_eq_zero_iff (two_ne_zero) |>.mp ha
    have hb' := pow_eq_zero_iff (two_ne_zero) |>.mp hb
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨ψ, hψ⟩ := exists_rotMat_eq hB
  have p11 := congrFun (congrFun hψ 0) 0
  have p12 := congrFun (congrFun hψ 0) 1
  have p21 := congrFun (congrFun hψ 1) 0
  have p22 := congrFun (congrFun hψ 1) 1
  simp [rotMat] at p11 p12 p21 p22
  refine ⟨ψ, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotX, h00, e01, e02, e10, e20] <;> linarith

/-- **The covering map is surjective.** -/
theorem cover_surjective : Function.Surjective cover := by
  intro R
  have hRorth := (mem_specialOrthogonalGroup_iff.mp R.2).1
  have h2 : (R.1)ᵀ * R.1 = 1 := (mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hRorth
  have hcol := congrFun (congrFun h2 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.one_apply_eq]
    at hcol
  obtain ⟨t, ht⟩ := exists_angle_elim (R.1 1 0) (R.1 2 0)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = sin t * R.1 1 0 + cos t * R.1 2 0 := ⟨_, rfl⟩
  have hr2 : R.1 0 0 ^ 2 + r ^ 2 = 1 := by
    have h := sin_sq_add_cos_sq t
    have e : r ^ 2 = (sin t ^ 2 + cos t ^ 2) * (R.1 1 0 ^ 2 + R.1 2 0 ^ 2)
        - (cos t * R.1 1 0 - sin t * R.1 2 0) ^ 2 := by
      rw [hr]
      ring
    rw [e, ht, h]
    linear_combination hcol
  obtain ⟨s, hcs, hss⟩ := exists_cos_sin hr2
  obtain ⟨g, hg⟩ : ∃ g : SU2, g = yEl (s / 2) * torus (t / 2) := ⟨_, rfl⟩
  have hcg : covMat g = rotY s * rotX t := by
    rw [hg, covMat_mul, covMat_yEl, covMat_torus]
    congr 2 <;> ring
  have hM00 : ((cover g * R : SO 3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 := by
    show (covMat g * R.1) 0 0 = 1
    rw [hcg]
    simp only [rotY, rotX, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one]
    simp
    linear_combination (R.1 0 0) * hcs + (sin t * R.1 1 0 + cos t * R.1 2 0) * hss
      - r * hr + hr2
  obtain ⟨ψ, hψ⟩ := eq_rotX_of_entry (cover g * R).2 hM00
  refine ⟨g⁻¹ * torus (ψ / 2), ?_⟩
  have h1 : cover (torus (ψ / 2)) = cover g * R := by
    apply Subtype.ext
    show covMat (torus (ψ / 2)) = _
    rw [covMat_torus, hψ]
    congr 1
    ring
  rw [map_mul, map_inv, h1, inv_mul_cancel_left]

/-! ### Trace and the positivity condition -/

theorem trace_covMat (q : SU2) : (covMat q).trace = 4 * (q.1 0 0).re ^ 2 - 1 := by
  have h := su2_norm_eq q
  rw [covMat, quatRot, Matrix.trace_fin_three_of]
  linarith

/-- If the symmetric part of the rotation `cover q` is positive semidefinite, then
`(Re q₀₀)² ≥ 1/2`: the rotation angle is at most `π/2`. -/
theorem one_le_of_posSemidef_symPart (q : SU2) (hP : (symPart (covMat q)).PosSemidef) :
    1 ≤ 2 * (q.1 0 0).re ^ 2 := by
  have hn := su2_norm_eq q
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (q.1 0 0).re := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (q.1 0 0).im := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (q.1 0 1).re := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (q.1 0 1).im := ⟨_, rfl⟩
  rw [covMat, ← hw, ← hx, ← hy, ← hz] at hP
  rw [← hw, ← hx, ← hy, ← hz] at hn
  rw [← hw]
  by_cases hxy : x ^ 2 + y ^ 2 = 0
  · have hx2 : x ^ 2 = 0 := by linarith [sq_nonneg x, sq_nonneg y]
    have hy2 : y ^ 2 = 0 := by linarith [sq_nonneg x, sq_nonneg y]
    have h := hP.dotProduct_mulVec_nonneg ![1, 0, 0]
    simp [symPart, quatRot, dotProduct, mulVec, Fin.sum_univ_three] at h
    nlinarith
  · have hpos : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hxy)
    have h := hP.dotProduct_mulVec_nonneg ![y, -x, 0]
    have e : star ![y, -x, 0] ⬝ᵥ (symPart (quatRot w x y z) *ᵥ ![y, -x, 0])
        = (x ^ 2 + y ^ 2) * (2 * w ^ 2 - 1) := by
      simp [symPart, quatRot, dotProduct, mulVec, Fin.sum_univ_three]
      linear_combination (-(x ^ 2 + y ^ 2)) * hn
    rw [e] at h
    have h3 : 0 ≤ 2 * w ^ 2 - 1 := nonneg_of_mul_nonneg_right h hpos
    linarith

end SOnMCMC

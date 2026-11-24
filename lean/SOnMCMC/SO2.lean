import SOnMCMC.CircleSampler
import SOnMCMC.Projection

/-!
# `SO(2)`: rotation matrices and the projection step

Paper: Section 4.2.

This file connects the circle model of `SOnMCMC.CircleSampler` to the matrix model of
`SOnMCMC.Projection` in dimension two:

* `rotMat` is a surjective homomorphism `ℝ → SO(2)` with kernel `2πℤ`, i.e. `SO(2) ≅ ℝ / 2πℤ`;
* a tangent step with coordinate `a` is the skew matrix `skew2 a`; an orthogonal matrix with
  that skew part exists only if `|a| ≤ 1` (`abs_le_one_of_skewPart_eq`);
* for `|a| ≤ 1` the rotation by `stepAngle a = arcsin a` is the principal projection: its skew
  part is `skew2 a` and its symmetric part is positive semidefinite (`principal_step_two`);
* for `|a| > 1` the step is the identity (`rotMat_stepAngle_of_lt`).
-/

open Real Matrix

namespace SOnMCMC

/-- The rotation matrix of angle `θ`. -/
noncomputable def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cos θ, -sin θ; sin θ, cos θ]

/-- The tangent step with coordinate `a`: the skew-symmetric matrix `a J`. -/
def skew2 (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -a; a, 0]

theorem rotMat_mem (θ : ℝ) : rotMat θ ∈ specialOrthogonalGroup (Fin 2) ℝ := by
  rw [rotMat, of_mem_specialOrthogonalGroup_fin_two_iff]
  refine ⟨rfl, by ring, ?_⟩
  nlinarith [sin_sq_add_cos_sq θ]

theorem rotMat_zero : rotMat 0 = 1 := by
  simp [rotMat, Matrix.one_fin_two]

/-- `θ ↦ rotMat θ` is a homomorphism. -/
theorem rotMat_add (θ φ : ℝ) : rotMat (θ + φ) = rotMat θ * rotMat φ := by
  simp only [rotMat, cos_add, sin_add, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Every element of `SO(2)` is a rotation matrix. -/
theorem exists_rotMat_eq {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M ∈ specialOrthogonalGroup (Fin 2) ℝ) : ∃ θ : ℝ, rotMat θ = M := by
  obtain ⟨h1, h2, h3⟩ := mem_specialOrthogonalGroup_fin_two_iff.mp hM
  set z : ℂ := ⟨M 0 0, M 1 0⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have h4 : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hz]
      rw [h2] at h3
      nlinarith
    have h5 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨Complex.arg z, ?_⟩
  have hc : cos (Complex.arg z) = M 0 0 := by
    rw [Complex.cos_arg hz0, hnorm, div_one]
  have hs : sin (Complex.arg z) = M 1 0 := by
    rw [Complex.sin_arg, hnorm, div_one]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rotMat, hc]
  · simp [rotMat, hs, h2]
  · simp [rotMat, hs]
  · simp [rotMat, hc, h1]

/-- The kernel of `θ ↦ rotMat θ` is `2πℤ`. -/
theorem rotMat_eq_one_iff (θ : ℝ) : rotMat θ = 1 ↔ ∃ k : ℤ, (k : ℝ) * (2 * π) = θ := by
  rw [← cos_eq_one_iff]
  constructor
  · intro h
    have := congrFun (congrFun h 0) 0
    simpa [rotMat] using this
  · intro h
    have hs : sin θ = 0 := by
      have := sin_sq_add_cos_sq θ
      rw [h] at this
      nlinarith
    simp [rotMat, h, hs, Matrix.one_fin_two]

theorem skewPart_rotMat (θ : ℝ) : skewPart (rotMat θ) = skew2 (sin θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewPart, rotMat, skew2] <;> ring

theorem symPart_rotMat (θ : ℝ) :
    symPart (rotMat θ) = diagonal (fun _ : Fin 2 => cos θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symPart, rotMat] <;> ring

theorem frobSq_skew2 (a : ℝ) : frobSq (skew2 a) = 2 * a ^ 2 := by
  simp [frobSq, skew2, Fin.sum_univ_two]
  ring

/-- **The projection exists only for short tangent steps.** If an orthogonal `2 × 2` matrix has
skew part `a J`, then `|a| ≤ 1`. -/
theorem abs_le_one_of_skewPart_eq {a : ℝ} {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : R ∈ orthogonalGroup (Fin 2) ℝ) (h : skewPart R = skew2 a) : |a| ≤ 1 := by
  have h1 := frobSq_skewPart_le_card hR
  rw [h, frobSq_skew2] at h1
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h1
  rw [abs_le]
  constructor <;> nlinarith

/-- **The accepted move is the rotation by `arcsin a`**, and it is the principal projection:
its skew part is the tangent step and its symmetric part is positive semidefinite. -/
theorem principal_step_two {a : ℝ} (h : |a| ≤ 1) :
    skewPart (rotMat (stepAngle a)) = skew2 a ∧
      (symPart (rotMat (stepAngle a))).PosSemidef := by
  have ha := abs_le.mp h
  constructor
  · rw [skewPart_rotMat, stepAngle_of_abs_le h, sin_arcsin ha.1 ha.2]
  · rw [symPart_rotMat, posSemidef_diagonal_iff]
    intro _
    rw [cos_stepAngle]
    simp only [h, ↓reduceIte]
    exact Real.sqrt_nonneg _

/-- A rejected proposal leaves the chain where it is. -/
theorem rotMat_stepAngle_of_lt {a : ℝ} (h : 1 < |a|) : rotMat (stepAngle a) = 1 := by
  rw [stepAngle_of_lt h, rotMat_zero]

end SOnMCMC

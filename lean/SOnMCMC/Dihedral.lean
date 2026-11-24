import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.RingTheory.SimpleRing.Principal
import SOnMCMC.FiniteWalk

/-!
# The random walk on the dihedral group `D_n`

Paper: Section 3.

The walk multiplies on the right by the identity with weight `a`, by the rotations `r^{±1}`
with weight `b/2` each, and by the reflection `s` with weight `c`.  We

* construct the two-dimensional representations `ρ_k` of `D_n`;
* compute the Fourier transform of the step weights at `ρ_k`;
* obtain `2n` eigenfunctions `φ_{k,ε}` with eigenvalues `a + b cos(2πk/n) + ε c`;
* prove that they form a complete family, so that these are *all* the eigenvalues;
* deduce the sharp Poincaré inequality: the spectral gap is `min (2c) (b (1 - cos (2π/n)))`.
-/

open Finset DihedralGroup
open scoped ComplexConjugate Real

namespace SOnMCMC

variable {n : ℕ} [NeZero n]

/-- The character `j ↦ exp(2πi j / n)` of `ℤ/n`. -/
noncomputable abbrev ψ (n : ℕ) [NeZero n] : AddChar (ZMod n) ℂ := ZMod.stdAddChar

theorem conj_ψ (j : ZMod n) : conj (ψ n j) = ψ n (-j) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

theorem ψ_add_ψ_neg (j : ZMod n) : ψ n j + ψ n (-j) = ((2 * (ψ n j).re : ℝ) : ℂ) := by
  rw [← conj_ψ, Complex.add_conj]

theorem ψ_mul_ψ_neg (j : ZMod n) : ψ n j * ψ n (-j) = 1 := by
  rw [← AddChar.map_add_eq_mul]
  simp

theorem sum_ψ_mul (b : ZMod n) : ∑ k : ZMod n, ψ n (k * b) = if b = 0 then (n : ℂ) else 0 := by
  have := AddChar.sum_mulShift (R' := ℂ) b (ZMod.isPrimitive_stdAddChar n)
  simpa [ZMod.card] using this

/-- `Re ψ(k) = cos(2π k / n)`. -/
theorem ψ_re (k : ZMod n) : (ψ n k).re = Real.cos (2 * π * k.val / n) := by
  have h : ψ n k = Complex.exp (2 * π * Complex.I * ((k.val : ℤ) : ℂ) / n) := by
    have := ZMod.stdAddChar_coe (N := n) (k.val : ℤ)
    rwa [Int.cast_natCast, ZMod.natCast_zmod_val] at this
  rw [h]
  have : (2 * π * Complex.I * ((k.val : ℤ) : ℂ) / n : ℂ)
      = ((2 * π * k.val / n : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- ASCII alias of `ψ_re`: the real part of `exp(2πi k / n)` is `cos(2π k / n)`. -/
theorem psi_re (k : ZMod n) : (ψ n k).re = Real.cos (2 * π * k.val / n) := ψ_re k

/-! ### The two-dimensional representations -/

/-- The underlying function of the representation `ρ_k`:
`ρ_k(r^i) = diag(ψ(ki), ψ(-ki))` and `ρ_k(s r^i) = antidiag(ψ(-ki), ψ(ki))`. -/
noncomputable def dihedralRepFun (k : ZMod n) : DihedralGroup n → Matrix (Fin 2) (Fin 2) ℂ
  | r i => !![ψ n (k * i), 0; 0, ψ n (-(k * i))]
  | sr i => !![0, ψ n (-(k * i)); ψ n (k * i), 0]

/-- **The representation `ρ_k` of `D_n`** on `ℂ²`. -/
noncomputable def dihedralRep (k : ZMod n) : DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := dihedralRepFun k
  map_one' := by
    rw [one_def]
    simp [dihedralRepFun, Matrix.one_fin_two]
  map_mul' := by
    rintro (i | i) (j | j)
    · simp only [r_mul_r, dihedralRepFun, Matrix.mul_fin_two, mul_zero, add_zero, zero_mul,
        zero_add, ← AddChar.map_add_eq_mul]
      congr 2 <;> ring_nf
    · simp only [r_mul_sr, dihedralRepFun, Matrix.mul_fin_two, mul_zero, add_zero, zero_mul,
        zero_add, ← AddChar.map_add_eq_mul]
      congr 2 <;> ring_nf
    · simp only [sr_mul_r, dihedralRepFun, Matrix.mul_fin_two, mul_zero, add_zero, zero_mul,
        zero_add, ← AddChar.map_add_eq_mul]
      congr 2 <;> ring_nf
    · simp only [sr_mul_sr, dihedralRepFun, Matrix.mul_fin_two, mul_zero, add_zero, zero_mul,
        zero_add, ← AddChar.map_add_eq_mul]
      congr 2 <;> ring_nf

theorem dihedralRep_r (k i : ZMod n) :
    dihedralRep k (r i) = !![ψ n (k * i), 0; 0, ψ n (-(k * i))] := rfl

theorem dihedralRep_sr (k i : ZMod n) :
    dihedralRep k (sr i) = !![0, ψ n (-(k * i)); ψ n (k * i), 0] := rfl

/-! ### The walk -/

/-- Step weights of the walk on `D_n`: weight `a` on the identity, `b/2` on each of `r`, `r⁻¹`,
and `c` on the reflection `s`. -/
noncomputable def dihedralStep (a b c : ℝ) : DihedralGroup n → ℂ :=
  (a : ℂ) • Pi.single 1 1 + ((b / 2 : ℝ) : ℂ) • (Pi.single (r 1) 1 + Pi.single (r (-1)) 1)
    + (c : ℂ) • Pi.single (sr 0) 1

/-- The walk operator in closed form. -/
theorem walkOp_dihedralStep (a b c : ℝ) (f : DihedralGroup n → ℂ) (x : DihedralGroup n) :
    walkOp (dihedralStep a b c) f x
      = a * f x + (b / 2 : ℝ) * (f (x * r 1) + f (x * r (-1))) + c * f (x * sr 0) := by
  simp only [dihedralStep, walkOp_add_left, walkOp_smul_left, walkOp_single, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, mul_one]

/-- The step weights sum to `a + b + c`. -/
theorem sum_dihedralStep (a b c : ℝ) :
    ∑ g : DihedralGroup n, dihedralStep a b c g = ((a + b + c : ℝ) : ℂ) := by
  simp only [dihedralStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ, ite_true]
  push_cast
  ring

omit [NeZero n] in
theorem dihedralStep_real (a b c : ℝ) (g : DihedralGroup n) :
    conj (dihedralStep a b c g) = dihedralStep a b c g := by
  simp only [dihedralStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    Complex.conj_ofReal, Pi.single_apply]
  split_ifs <;> simp

omit [NeZero n] in
theorem dihedralStep_symm (a b c : ℝ) (g : DihedralGroup n) :
    dihedralStep a b c g⁻¹ = dihedralStep a b c g := by
  have h1 : ∀ h : DihedralGroup n, (g⁻¹ = h) = (g = h⁻¹) := fun h => by
    rw [inv_eq_iff_eq_inv]
  simp only [dihedralStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, h1,
    inv_one, inv_r, inv_sr, neg_neg]
  ring

/-- **Fourier transform of the step weights at `ρ_k`:**
`μ̂(ρ_k) = (a + b cos(2πk/n)) I + c S` with `S` the swap matrix. -/
theorem fourierTransform_dihedralRep (a b c : ℝ) (k : ZMod n) :
    fourierTransform (dihedralStep a b c) (dihedralRep k)
      = !![((a + b * (ψ n k).re : ℝ) : ℂ), (c : ℂ); (c : ℂ), ((a + b * (ψ n k).re : ℝ) : ℂ)] := by
  have key : ∀ (μ : DihedralGroup n → ℂ) (g : DihedralGroup n),
      fourierTransform (Pi.single g 1 : DihedralGroup n → ℂ) (dihedralRep k) = dihedralRep k g := by
    intro _ g
    simp [fourierTransform, Pi.single_apply]
  have hlin : fourierTransform (dihedralStep a b c) (dihedralRep k)
      = (a : ℂ) • dihedralRep k 1
        + ((b / 2 : ℝ) : ℂ) • (dihedralRep k (r 1) + dihedralRep k (r (-1)))
        + (c : ℂ) • dihedralRep k (sr 0) := by
    simp only [fourierTransform, dihedralStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, smul_add]
    have h := fun g => key (dihedralStep a b c) g
    simp only [fourierTransform] at h
    simp only [h]
  rw [hlin, map_one, dihedralRep_r, dihedralRep_r, dihedralRep_sr]
  have h2 := ψ_add_ψ_neg (n := n) k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_fin_two] <;>
    · first
      | (rw [h2]; push_cast; ring)
      | (rw [add_comm, h2]; push_cast; ring)

/-- Sign attached to a Boolean: `true ↦ +1`, `false ↦ -1`. -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

theorem sgn_mul_self (s : Bool) : sgn s * sgn s = 1 := by cases s <;> simp [sgn]

@[simp] theorem sgn_true : sgn true = 1 := by simp [sgn]

@[simp] theorem sgn_false : sgn false = -1 := by simp [sgn]

/-- **The eigenvalues** `a + b cos(2πk/n) ± c`. -/
noncomputable def dihedralEig (a b c : ℝ) (j : ZMod n × Bool) : ℝ :=
  a + b * (ψ n j.1).re + sgn j.2 * c

/-- **The eigenfunctions** `φ_{k,ε}`: the first coordinate of `x ↦ ρ_k(x) (1, ε)`. -/
noncomputable def dihedralEigFun (j : ZMod n × Bool) : DihedralGroup n → ℂ :=
  fun x => (dihedralRep j.1 x).mulVec ![1, (sgn j.2 : ℂ)] 0

theorem dihedralEigFun_r (k : ZMod n) (s : Bool) (i : ZMod n) :
    dihedralEigFun (k, s) (r i) = ψ n (k * i) := by
  simp [dihedralEigFun, dihedralRep_r, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem dihedralEigFun_sr (k : ZMod n) (s : Bool) (i : ZMod n) :
    dihedralEigFun (k, s) (sr i) = sgn s * ψ n (-(k * i)) := by
  simp [dihedralEigFun, dihedralRep_sr, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

/-- **Eigenfunction equation**, obtained from the eigenvectors `(1, ±1)` of `μ̂(ρ_k)`. -/
theorem walkOp_dihedralEigFun (a b c : ℝ) (j : ZMod n × Bool) :
    walkOp (dihedralStep a b c) (dihedralEigFun j)
      = fun x => (dihedralEig a b c j : ℂ) * dihedralEigFun j x := by
  obtain ⟨k, s⟩ := j
  refine walkOp_eigenfunction (dihedralStep a b c) (dihedralRep k) ![1, (sgn s : ℂ)]
    (dihedralEig a b c (k, s) : ℂ) ?_ 0
  rw [fourierTransform_dihedralRep]
  have hs : (sgn s : ℂ) * sgn s = 1 := by exact_mod_cast sgn_mul_self s
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, dihedralEig]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, dihedralEig]
    linear_combination (-(c : ℂ)) * hs

/-- Sums over `D_n` split into rotations and reflections. -/
theorem sum_dihedral (F : DihedralGroup n → ℂ) :
    ∑ x, F x = ∑ i : ZMod n, F (r i) + ∑ i : ZMod n, F (sr i) := by
  rw [← Fintype.sum_equiv (equivSum (n := n)).symm (fun y => F ((equivSum (n := n)).symm y)) F
    (fun _ => rfl), Fintype.sum_sum_type]
  rfl

/-- **Completeness** of the family `φ_{k,ε}`. -/
theorem dihedral_complete : IsCompleteFamily (dihedralEigFun (n := n)) (2 * n) := by
  have hsum : ∀ F : ZMod n × Bool → ℂ,
      ∑ j, F j = ∑ k : ZMod n, (F (k, true) + F (k, false)) := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_bool]
  rintro (i | i) (j | j)
  · rw [hsum]
    simp only [dihedralEigFun_r, conj_ψ]
    have : ∀ k : ZMod n, ψ n (k * i) * ψ n (-(k * j)) + ψ n (k * i) * ψ n (-(k * j))
        = 2 * ψ n (k * (i - j)) := by
      intro k
      rw [← AddChar.map_add_eq_mul]
      ring_nf
    simp only [this, ← Finset.mul_sum, sum_ψ_mul, sub_eq_zero]
    by_cases h : i = j
    · simp [h]
    · have : (r i : DihedralGroup n) ≠ r j := fun hh => h (r.inj hh)
      simp [h, this]
  · rw [hsum]
    simp [dihedralEigFun_r, dihedralEigFun_sr]
  · rw [hsum]
    simp [dihedralEigFun_r, dihedralEigFun_sr]
  · rw [hsum]
    simp only [dihedralEigFun_sr, map_mul, Complex.conj_ofReal, conj_ψ, neg_neg]
    have : ∀ k : ZMod n,
        (sgn true : ℂ) * ψ n (-(k * i)) * ((sgn true : ℂ) * ψ n (k * j))
          + (sgn false : ℂ) * ψ n (-(k * i)) * ((sgn false : ℂ) * ψ n (k * j))
        = 2 * ψ n (k * (j - i)) := by
      intro k
      have h : ψ n (-(k * i)) * ψ n (k * j) = ψ n (k * (j - i)) := by
        rw [← AddChar.map_add_eq_mul]
        ring_nf
      rw [sgn_true, sgn_false]
      push_cast
      linear_combination 2 * h
    simp only [this, ← Finset.mul_sum, sum_ψ_mul, sub_eq_zero]
    by_cases h : i = j
    · simp [h]
    · have h' : ¬ j = i := fun hh => h hh.symm
      have : (sr i : DihedralGroup n) ≠ sr j := fun hh => h (sr.inj hh)
      simp [h', this]

/-- `φ_{0,+}` is the constant function `1`. -/
theorem dihedralEigFun_zero_true (x : DihedralGroup n) : dihedralEigFun ((0 : ZMod n), true) x = 1 := by
  cases x with
  | r i => simp [dihedralEigFun_r]
  | sr i => simp [dihedralEigFun_sr, sgn]

/-- Every other `φ_{k,ε}` has mean zero. -/
theorem sum_dihedralEigFun (j : ZMod n × Bool) (hj : j ≠ (0, true)) :
    ∑ x, dihedralEigFun j x = 0 := by
  obtain ⟨k, s⟩ := j
  rw [sum_dihedral]
  simp only [dihedralEigFun_r, dihedralEigFun_sr, ← Finset.mul_sum]
  have h1 : ∑ i : ZMod n, ψ n (k * i) = if k = 0 then (n : ℂ) else 0 := by
    simpa [mul_comm] using sum_ψ_mul (n := n) k
  have h2 : ∑ i : ZMod n, ψ n (-(k * i)) = if k = 0 then (n : ℂ) else 0 := by
    have := sum_ψ_mul (n := n) (-k)
    simpa [mul_comm, neg_eq_zero] using this
  rw [h1, h2]
  by_cases hk : k = 0
  · subst hk
    cases s
    · simp [sgn]
    · exact absurd rfl hj
  · simp [hk]

/-- `∑ |φ_{k,ε}|² = 2n`. -/
theorem sum_normSq_dihedralEigFun (j : ZMod n × Bool) :
    ∑ x, ‖dihedralEigFun j x‖ ^ 2 = 2 * n := by
  obtain ⟨k, s⟩ := j
  have hψ : ∀ t : ZMod n, ‖ψ n t‖ = 1 := fun t => by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hs : |sgn s| = 1 := by cases s <;> simp [sgn]
  have key : ∀ x : DihedralGroup n, ‖dihedralEigFun (k, s) x‖ ^ 2 = 1 := by
    intro x
    cases x with
    | r i => simp [dihedralEigFun_r, hψ]
    | sr i => simp [dihedralEigFun_sr, hψ, hs]
  simp only [key, Finset.sum_const, Finset.card_univ, DihedralGroup.card]
  simp

/-! ### Spectrum and spectral gap -/

/-- **The spectrum of the walk on `D_n`.** A complex number is an eigenvalue of the walk operator
if and only if it is one of `a + b cos(2πk/n) ± c`. -/
theorem dihedral_spectrum (a b c : ℝ) (z : ℂ) :
    (∃ f : DihedralGroup n → ℂ, f ≠ 0 ∧ walkOp (dihedralStep a b c) f = fun x => z * f x)
      ↔ ∃ j : ZMod n × Bool, z = dihedralEig a b c j := by
  constructor
  · rintro ⟨f, hf, hPf⟩
    have hN : (0 : ℝ) < 2 * n := by
      have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
      linarith
    exact eigenvalue_mem_of_eigenbasis hN dihedral_complete (dihedralStep a b c)
      (dihedralStep_real a b c) (dihedralStep_symm a b c) (dihedralEig a b c)
      (walkOp_dihedralEigFun a b c) z f hf hPf
  · rintro ⟨j, rfl⟩
    refine ⟨dihedralEigFun j, ?_, walkOp_dihedralEigFun a b c j⟩
    intro h
    obtain ⟨k, s⟩ := j
    have := congrFun h (r 0)
    rw [dihedralEigFun_r] at this
    simp at this

/-- For `k ≠ 0`, `cos(2πk/n) ≤ cos(2π/n)`. -/
theorem ψ_re_le (k : ZMod n) (hk : k ≠ 0) : (ψ n k).re ≤ Real.cos (2 * π / n) := by
  rw [ψ_re]
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hv1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr (by simpa using hk)
  have hv2 : k.val + 1 ≤ n := ZMod.val_lt k
  have hv1' : (1 : ℝ) ≤ k.val := by exact_mod_cast hv1
  have hv2' : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast hv2
  have hn2 : (2 : ℝ) ≤ n := by linarith
  have hπ := Real.pi_pos
  have hx0 : 0 ≤ 2 * π / n := by positivity
  have hxle : 2 * π / n ≤ 2 * π * k.val / n := by
    apply div_le_div_of_nonneg_right _ hn.le
    nlinarith
  by_cases hcase : 2 * π * k.val / n ≤ π
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hx0 hcase hxle
  · push Not at hcase
    have h1 : Real.cos (2 * π * k.val / n) = Real.cos (2 * π - 2 * π * k.val / n) := by
      rw [Real.cos_two_pi_sub]
    rw [h1]
    refine Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith) ?_
    have : 2 * π - 2 * π * k.val / n = 2 * π * (n - k.val) / n := by
      field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ hn.le
    nlinarith

/-- The spectral gap of the walk on `D_n`. -/
noncomputable def dihedralGap (n : ℕ) (b c : ℝ) : ℝ := min (2 * c) (b * (1 - Real.cos (2 * π / n)))

/-- Every eigenvalue other than the trivial one is at most `1 - gap`. -/
theorem dihedralEig_le (a b c : ℝ) (habc : a + b + c = 1) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (j : ZMod n × Bool) (hj : j ≠ (0, true)) :
    dihedralEig a b c j ≤ 1 - dihedralGap n b c := by
  obtain ⟨k, s⟩ := j
  have hcos1 : (ψ n k).re ≤ 1 := by
    rw [ψ_re]
    exact Real.cos_le_one _
  simp only [dihedralEig, dihedralGap]
  by_cases hk : k = 0
  · subst hk
    cases s
    · have : (ψ n (0 : ZMod n)).re = 1 := by simp
      have hmin := min_le_left (2 * c) (b * (1 - Real.cos (2 * π / n)))
      rw [this, sgn_false]
      linarith
    · exact absurd rfl hj
  · have h1 := ψ_re_le k hk
    have hmin := min_le_right (2 * c) (b * (1 - Real.cos (2 * π / n)))
    have hs : sgn s * c ≤ c := by
      cases s
      · rw [sgn_false]; linarith
      · rw [sgn_true]; linarith
    nlinarith

/-- **Theorem (Poincaré inequality on `D_n`).** For every mean-zero `f : D_n → ℂ`,
`Re ⟨f, P f⟩ ≤ (1 - γ) ⟨f, f⟩` with `γ = min (2c) (b (1 - cos (2π/n)))`. -/
theorem dihedral_poincare (a b c : ℝ) (habc : a + b + c = 1) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (f : DihedralGroup n → ℂ) (hf : ∑ x, f x = 0) :
    (∑ x, conj (f x) * walkOp (dihedralStep a b c) f x).re
      ≤ (1 - dihedralGap n b c) * ∑ x, ‖f x‖ ^ 2 := by
  have hN : (0 : ℝ) < 2 * n := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    linarith
  exact poincare_of_eigenbasis hN dihedral_complete (dihedralStep a b c) (dihedralEig a b c)
    (walkOp_dihedralEigFun a b c) (0, true) dihedralEigFun_zero_true _
    (fun j hj => dihedralEig_le a b c habc hb hc j hj) f hf

/-- **Theorem (sharpness).** For `n ≥ 2` the constant in `dihedral_poincare` is attained by a
nonzero mean-zero function, so `min (2c) (b (1 - cos (2π/n)))` is exactly the spectral gap. -/
theorem dihedral_poincare_sharp (hn : 2 ≤ n) (a b c : ℝ) (habc : a + b + c = 1) :
    ∃ f : DihedralGroup n → ℂ, f ≠ 0 ∧ ∑ x, f x = 0 ∧
      (∑ x, conj (f x) * walkOp (dihedralStep a b c) f x).re
        = (1 - dihedralGap n b c) * ∑ x, ‖f x‖ ^ 2 := by
  have h1ne : (1 : ZMod n) ≠ 0 := by
    have : Fact (1 < n) := ⟨hn⟩
    exact one_ne_zero
  -- the quadratic form on an eigenfunction
  have hquad : ∀ j : ZMod n × Bool,
      (∑ x, conj (dihedralEigFun j x) * walkOp (dihedralStep a b c) (dihedralEigFun j) x).re
        = dihedralEig a b c j * ∑ x, ‖dihedralEigFun j x‖ ^ 2 := by
    intro j
    rw [walkOp_dihedralEigFun]
    have : ∀ x, conj (dihedralEigFun j x) * ((dihedralEig a b c j : ℂ) * dihedralEigFun j x)
        = ((dihedralEig a b c j * ‖dihedralEigFun j x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [mul_left_comm, conj_mul_eq_normSq]
      push_cast
      ring
    simp only [this, ← Complex.ofReal_sum, Complex.ofReal_re, Finset.mul_sum]
  have hne : ∀ j : ZMod n × Bool, dihedralEigFun j ≠ 0 := by
    rintro ⟨k, s⟩ h
    have := congrFun h (r 0)
    rw [dihedralEigFun_r] at this
    simp at this
  have hψ1 : (ψ n (1 : ZMod n)).re = Real.cos (2 * π / n) := by
    rw [ψ_re]
    have : Fact (1 < n) := ⟨hn⟩
    rw [ZMod.val_one]
    simp
  by_cases hcase : 2 * c ≤ b * (1 - Real.cos (2 * π / n))
  · refine ⟨dihedralEigFun (0, false), hne _, sum_dihedralEigFun _ (by simp), ?_⟩
    rw [hquad]
    congr 1
    simp only [dihedralEig, dihedralGap, min_eq_left hcase]
    have : (ψ n (0 : ZMod n)).re = 1 := by simp
    rw [this, sgn_false]
    linarith
  · push Not at hcase
    refine ⟨dihedralEigFun (1, true), hne _, sum_dihedralEigFun _ (by simp [h1ne]), ?_⟩
    rw [hquad]
    congr 1
    simp only [dihedralEig, dihedralGap, min_eq_right hcase.le, hψ1]
    rw [sgn_true]
    linarith

end SOnMCMC

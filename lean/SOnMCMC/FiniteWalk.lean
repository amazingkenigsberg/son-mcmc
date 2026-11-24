import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Random walks on finite groups and their Fourier analysis

Paper: Section 2.1 ("Random walks on finite groups").

For a finite group `G` and step weights `μ : G → 𝕜`, the right random walk has Markov operator
`(P f)(x) = ∑ g, μ g * f (x * g)`.  This file proves, with no hypotheses beyond those stated:

* the uniform distribution is stationary, and the walk is reversible when `μ` is symmetric;
* composition of walk operators is the walk operator of the convolution;
* matrix coefficients of a representation `ρ` are mapped by `P` to matrix coefficients of
  `ρ · μ̂(ρ)`, where `μ̂(ρ) = ∑ g, μ g • ρ g` is the Fourier transform;
* eigenvectors of `μ̂(ρ)` give eigenfunctions of `P`;
* `μ̂(ρ)` commutes with `ρ` when `μ` is a class function;
* a complete family of eigenfunctions yields a Poincaré inequality and pins down the spectrum.
-/

open Finset
open scoped ComplexConjugate

namespace SOnMCMC

section Basic

variable {G : Type*} [Group G] [Fintype G] {𝕜 : Type*} [CommRing 𝕜]

/-- The Markov operator of the right random walk on `G` with step weights `μ`:
`(P f)(x) = ∑ g, μ g * f (x * g)`. -/
def walkOp (μ : G → 𝕜) (f : G → 𝕜) : G → 𝕜 := fun x => ∑ g, μ g * f (x * g)

theorem walkOp_apply (μ f : G → 𝕜) (x : G) : walkOp μ f x = ∑ g, μ g * f (x * g) := rfl

/-- Constants are fixed by the walk operator of a probability vector. -/
theorem walkOp_const (μ : G → 𝕜) (hμ : ∑ g, μ g = 1) (c : 𝕜) :
    walkOp μ (fun _ => c) = fun _ => c := by
  funext x
  simp [walkOp, ← Finset.sum_mul, hμ]

theorem walkOp_add (μ f h : G → 𝕜) : walkOp μ (f + h) = walkOp μ f + walkOp μ h := by
  funext x
  simp [walkOp, mul_add, Finset.sum_add_distrib]

theorem walkOp_smul (μ : G → 𝕜) (c : 𝕜) (f : G → 𝕜) : walkOp μ (c • f) = c • walkOp μ f := by
  funext x
  simp [walkOp, Finset.mul_sum, mul_left_comm]

theorem walkOp_sum {J : Type*} (s : Finset J) (μ : G → 𝕜) (F : J → G → 𝕜) :
    walkOp μ (fun x => ∑ j ∈ s, F j x) = fun x => ∑ j ∈ s, walkOp μ (F j) x := by
  funext x
  simp only [walkOp, Finset.mul_sum]
  exact Finset.sum_comm

theorem walkOp_add_left (μ ν f : G → 𝕜) : walkOp (μ + ν) f = walkOp μ f + walkOp ν f := by
  funext x
  simp [walkOp, add_mul, Finset.sum_add_distrib]

theorem walkOp_smul_left (c : 𝕜) (μ f : G → 𝕜) : walkOp (c • μ) f = c • walkOp μ f := by
  funext x
  simp [walkOp, Finset.mul_sum, mul_assoc]

/-- The walk operator of a point mass at `g` is right translation by `g`. -/
theorem walkOp_single [DecidableEq G] (g : G) (f : G → 𝕜) :
    walkOp (Pi.single g 1) f = fun x => f (x * g) := by
  funext x
  simp [walkOp, Pi.single_apply]

/-- **Stationarity of the uniform distribution.** -/
theorem sum_walkOp (μ f : G → 𝕜) : ∑ x, walkOp μ f x = (∑ g, μ g) * ∑ x, f x := by
  simp only [walkOp]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => rfl)

/-- **Reversibility.** If the step weights are symmetric (`μ g⁻¹ = μ g`), the walk operator is
symmetric for the bilinear pairing `∑ x, f x * h x`. -/
theorem sum_walkOp_mul (μ : G → 𝕜) (hμ : ∀ g, μ g⁻¹ = μ g) (f h : G → 𝕜) :
    ∑ x, walkOp μ f x * h x = ∑ x, f x * walkOp μ h x := by
  simp only [walkOp, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  calc ∑ g, ∑ x, μ g * f (x * g) * h x
      = ∑ g, ∑ x, μ g * f x * h (x * g⁻¹) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => by simp)
    _ = ∑ g, ∑ x, μ g * f x * h (x * g) := by
        refine Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => ?_)
        simp [hμ]
    _ = ∑ g, ∑ x, f x * (μ g * h (x * g)) := by
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun x _ => ?_
        ring

/-- Convolution of step weights: the law of the product of two independent steps. -/
def conv (μ ν : G → 𝕜) : G → 𝕜 := fun g => ∑ h, μ h * ν (h⁻¹ * g)

/-- Two steps of the walk: `P_μ ∘ P_ν = P_{μ * ν}`. -/
theorem walkOp_walkOp (μ ν f : G → 𝕜) : walkOp μ (walkOp ν f) = walkOp (conv μ ν) f := by
  funext x
  simp only [walkOp, conv, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun k => ?_)
  simp [mul_assoc]

end Basic

section Fourier

variable {G : Type*} [Group G] [Fintype G] {𝕜 : Type*} [CommRing 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Fourier transform of the step weights `μ` at a matrix representation `ρ`:
`μ̂(ρ) = ∑ g, μ g • ρ g`. -/
def fourierTransform (μ : G → 𝕜) (ρ : G →* Matrix ι ι 𝕜) : Matrix ι ι 𝕜 := ∑ g, μ g • ρ g

/-- **Matrix coefficients are invariant.** `P ρ_{ij} = (ρ · μ̂(ρ))_{ij}`. -/
theorem walkOp_matrixCoeff (μ : G → 𝕜) (ρ : G →* Matrix ι ι 𝕜) (i j : ι) :
    walkOp μ (fun x => ρ x i j) = fun x => (ρ x * fourierTransform μ ρ) i j := by
  funext x
  simp only [walkOp, fourierTransform, map_mul, Matrix.mul_sum, Matrix.sum_apply,
    Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]

/-- **Eigenvectors of the Fourier transform give eigenfunctions of the walk.**
If `μ̂(ρ) v = c v`, then each coordinate of `x ↦ ρ(x) v` is an eigenfunction with eigenvalue `c`. -/
theorem walkOp_eigenfunction (μ : G → 𝕜) (ρ : G →* Matrix ι ι 𝕜) (v : ι → 𝕜) (c : 𝕜)
    (hv : (fourierTransform μ ρ).mulVec v = c • v) (i : ι) :
    walkOp μ (fun x => (ρ x).mulVec v i) = fun x => c * (ρ x).mulVec v i := by
  funext x
  have h1 : walkOp μ (fun y => (ρ y).mulVec v i) x
      = ((ρ x * fourierTransform μ ρ).mulVec v) i := by
    simp only [walkOp, fourierTransform, map_mul, Matrix.mul_sum, Matrix.sum_mulVec,
      Matrix.mul_smul, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rfl

/-- **Schur-type commutation.** If `μ` is a class function then `μ̂(ρ)` commutes with `ρ`. -/
theorem fourierTransform_comm_of_class (μ : G → 𝕜) (hμ : ∀ g h, μ (h * g * h⁻¹) = μ g)
    (ρ : G →* Matrix ι ι 𝕜) (h : G) :
    ρ h * fourierTransform μ ρ = fourierTransform μ ρ * ρ h := by
  simp only [fourierTransform, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← map_mul]
  refine Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ (fun g => ?_)
  simp [hμ]

/-- The Fourier transform turns convolution into matrix multiplication. -/
theorem fourierTransform_conv (μ ν : G → 𝕜) (ρ : G →* Matrix ι ι 𝕜) :
    fourierTransform (conv μ ν) ρ = fourierTransform μ ρ * fourierTransform ν ρ := by
  calc fourierTransform (conv μ ν) ρ = ∑ g, ∑ h, (μ h * ν (h⁻¹ * g)) • ρ g := by
        simp only [fourierTransform, conv, Finset.sum_smul]
    _ = ∑ h, ∑ g, (μ h * ν (h⁻¹ * g)) • ρ g := Finset.sum_comm
    _ = ∑ h, ∑ k, (μ h * ν k) • ρ (h * k) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g => ?_)
        simp
    _ = fourierTransform μ ρ * fourierTransform ν ρ := by
        simp only [fourierTransform, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
          Matrix.mul_smul, map_mul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun h _ => ?_
        rw [mul_comm]

end Fourier

section Eigenbasis

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {J : Type*} [Fintype J]

/-- Fourier coefficient of `f` against the family `φ`. -/
def coeff (φ : J → G → ℂ) (f : G → ℂ) (j : J) : ℂ := ∑ y, conj (φ j y) * f y

/-- A family `φ` is *complete with constant `N`* if `∑ j, φ j x * conj (φ j y) = N · [x = y]`. -/
def IsCompleteFamily (φ : J → G → ℂ) (N : ℝ) : Prop :=
  ∀ x y, ∑ j, φ j x * conj (φ j y) = if x = y then (N : ℂ) else 0

omit [Group G] in
/-- Fourier inversion for a complete family. -/
theorem expansion_of_complete {φ : J → G → ℂ} {N : ℝ} (hφ : IsCompleteFamily φ N)
    (f : G → ℂ) (x : G) : ∑ j, coeff φ f j * φ j x = N * f x := by
  simp only [coeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y, ∑ j, conj (φ j y) * f y * φ j x = (if x = y then (N : ℂ) else 0) * f y := by
    intro y
    rw [← hφ x y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp [this]

omit [Group G] [DecidableEq G] in
/-- Parseval-type identity: pairing against `f` of an expansion in the family. -/
theorem sum_conj_mul_expansion (φ : J → G → ℂ) (f : G → ℂ) (a : J → ℂ) :
    ∑ x, conj (f x) * ∑ j, a j * φ j x = ∑ j, a j * conj (coeff φ f j) := by
  simp only [coeff, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
  ring

omit [Group G] in
/-- Parseval for a complete family. -/
theorem parseval_of_complete {φ : J → G → ℂ} {N : ℝ} (hφ : IsCompleteFamily φ N)
    (f : G → ℂ) : (N : ℂ) * ∑ x, conj (f x) * f x = ∑ j, coeff φ f j * conj (coeff φ f j) := by
  rw [← sum_conj_mul_expansion φ f (coeff φ f), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [expansion_of_complete hφ f x]
  ring

/-- The quadratic form of the walk operator in a complete family of eigenfunctions. -/
theorem quadratic_form_of_eigenbasis {φ : J → G → ℂ} {N : ℝ} (hφ : IsCompleteFamily φ N)
    (μ : G → ℂ) (lam : J → ℝ) (heig : ∀ j, walkOp μ (φ j) = fun x => (lam j : ℂ) * φ j x)
    (f : G → ℂ) :
    (N : ℂ) * ∑ x, conj (f x) * walkOp μ f x
      = ∑ j, (lam j : ℂ) * (coeff φ f j * conj (coeff φ f j)) := by
  have hNf : (fun x => (N : ℂ) * f x) = fun x => ∑ j, coeff φ f j * φ j x := by
    funext x
    exact (expansion_of_complete hφ f x).symm
  have hP : ∀ x, (N : ℂ) * walkOp μ f x = ∑ j, (lam j * coeff φ f j) * φ j x := by
    intro x
    have h1 : walkOp μ (fun y => (N : ℂ) * f y) x = (N : ℂ) * walkOp μ f x := by
      have := congrFun (walkOp_smul μ (N : ℂ) f) x
      simpa [Pi.smul_def] using this
    rw [← h1, hNf]
    have h2 : (fun y => ∑ j, coeff φ f j * φ j y)
        = fun y => ∑ j ∈ Finset.univ, (coeff φ f j • φ j) y := by
      funext y
      simp
    rw [h2, walkOp_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [walkOp_smul, Pi.smul_apply, heig j]
    simp only [smul_eq_mul]
    ring
  rw [Finset.mul_sum]
  calc ∑ x, (N : ℂ) * (conj (f x) * walkOp μ f x)
      = ∑ x, conj (f x) * ∑ j, (lam j * coeff φ f j) * φ j x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← hP x]
        ring
    _ = ∑ j, (lam j * coeff φ f j) * conj (coeff φ f j) := sum_conj_mul_expansion φ f _
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

theorem mul_conj_eq_normSq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem conj_mul_eq_normSq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, mul_conj_eq_normSq]

/-- **Poincaré inequality from a complete family of eigenfunctions.**
If `φ` is a complete family of eigenfunctions of the walk with real eigenvalues `lam`, `φ j₀` is
the constant function, and every other eigenvalue is at most `Λ`, then for every mean-zero `f`
`Re ⟨f, P f⟩ ≤ Λ ⟨f, f⟩`. -/
theorem poincare_of_eigenbasis {φ : J → G → ℂ} {N : ℝ} (hN : 0 < N)
    (hφ : IsCompleteFamily φ N) (μ : G → ℂ) (lam : J → ℝ)
    (heig : ∀ j, walkOp μ (φ j) = fun x => (lam j : ℂ) * φ j x)
    (j₀ : J) (hj₀ : ∀ x, φ j₀ x = 1) (Λ : ℝ) (hΛ : ∀ j, j ≠ j₀ → lam j ≤ Λ)
    (f : G → ℂ) (hf : ∑ x, f x = 0) :
    (∑ x, conj (f x) * walkOp μ f x).re ≤ Λ * ∑ x, ‖f x‖ ^ 2 := by
  have hc0 : coeff φ f j₀ = 0 := by simp [coeff, hj₀, hf]
  have hQ := quadratic_form_of_eigenbasis hφ μ lam heig f
  have hPar := parseval_of_complete hφ f
  -- take real parts
  have hQre : N * (∑ x, conj (f x) * walkOp μ f x).re
      = ∑ j, lam j * ‖coeff φ f j‖ ^ 2 := by
    have := congrArg Complex.re hQ
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.re_sum, mul_conj_eq_normSq] at this
    simpa using this
  have hParre : N * ∑ x, ‖f x‖ ^ 2 = ∑ j, ‖coeff φ f j‖ ^ 2 := by
    have := congrArg Complex.re hPar
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.re_sum, mul_conj_eq_normSq, conj_mul_eq_normSq] at this
    simpa using this
  have hle : ∑ j, lam j * ‖coeff φ f j‖ ^ 2 ≤ ∑ j, Λ * ‖coeff φ f j‖ ^ 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj
      simp [hc0]
    · exact mul_le_mul_of_nonneg_right (hΛ j hj) (by positivity)
  rw [← Finset.mul_sum, ← hParre, ← hQre] at hle
  have : N * (∑ x, conj (f x) * walkOp μ f x).re ≤ N * (Λ * ∑ x, ‖f x‖ ^ 2) := by
    calc N * (∑ x, conj (f x) * walkOp μ f x).re ≤ Λ * (N * ∑ x, ‖f x‖ ^ 2) := hle
      _ = N * (Λ * ∑ x, ‖f x‖ ^ 2) := by ring
  exact le_of_mul_le_mul_left this hN

omit [DecidableEq G] in
/-- Hermitian symmetry of the walk operator for real symmetric step weights. -/
theorem sum_conj_mul_walkOp (μ : G → ℂ) (hμr : ∀ g, conj (μ g) = μ g) (hμs : ∀ g, μ g⁻¹ = μ g)
    (f h : G → ℂ) :
    ∑ x, conj (h x) * walkOp μ f x = ∑ x, conj (walkOp μ h x) * f x := by
  have hconj : (fun x => conj (walkOp μ h x)) = walkOp μ (fun x => conj (h x)) := by
    funext x
    simp [walkOp, hμr]
  have := sum_walkOp_mul μ hμs f (fun x => conj (h x))
  calc ∑ x, conj (h x) * walkOp μ f x = ∑ x, walkOp μ f x * conj (h x) := by
        refine Finset.sum_congr rfl fun x _ => mul_comm _ _
    _ = ∑ x, f x * walkOp μ (fun x => conj (h x)) x := this
    _ = ∑ x, conj (walkOp μ h x) * f x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← congrFun hconj x, mul_comm]

/-- **The spectrum is exhausted by a complete family of eigenfunctions.**
For real symmetric step weights, any eigenvalue of the walk operator is one of the `lam j`. -/
theorem eigenvalue_mem_of_eigenbasis {φ : J → G → ℂ} {N : ℝ} (hN : 0 < N)
    (hφ : IsCompleteFamily φ N) (μ : G → ℂ)
    (hμr : ∀ g, conj (μ g) = μ g) (hμs : ∀ g, μ g⁻¹ = μ g) (lam : J → ℝ)
    (heig : ∀ j, walkOp μ (φ j) = fun x => (lam j : ℂ) * φ j x)
    (c : ℂ) (f : G → ℂ) (hf : f ≠ 0) (hPf : walkOp μ f = fun x => c * f x) :
    ∃ j, c = lam j := by
  by_contra hne
  simp only [not_exists] at hne
  have hcoeff : ∀ j, coeff φ f j = 0 := by
    intro j
    have h1 : ∑ x, conj (φ j x) * walkOp μ f x = c * coeff φ f j := by
      simp only [hPf, coeff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have h2 : ∑ x, conj (φ j x) * walkOp μ f x = (lam j : ℂ) * coeff φ f j := by
      rw [sum_conj_mul_walkOp μ hμr hμs f (φ j), heig j]
      simp only [coeff, Finset.mul_sum, map_mul, Complex.conj_ofReal]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have h3 : (c - lam j) * coeff φ f j = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) (hne j)
    · exact h
  apply hf
  funext x
  have := expansion_of_complete hφ f x
  simp only [hcoeff, zero_mul, Finset.sum_const_zero] at this
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simpa [hN'] using this.symm

end Eigenbasis

end SOnMCMC

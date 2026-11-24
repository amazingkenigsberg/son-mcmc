import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import SOnMCMC.SU2

/-!
# Harmonic analysis on `SU(2)`: the eigenfunction spaces and their completeness

Paper: Section 6.2.

For `k ≥ 0` let `harm k` be the span of the functions `x ↦ (uᵀ x v)^k` on `SU(2)`, `u, v ∈ ℂ²`.
(This is the space of matrix coefficients of the irreducible representation of dimension
`k + 1`, but we never use that.)  The main result of this file is completeness:

* `lin_mul_lin_pow_succ_mem`: multiplying an element of `harm (k+1)` by a linear form gives an
  element of `harm (k+2) ⊔ harm k`;
* `mul_mem_harmAll`: hence `harmAll = ⨆ k, harm k` is closed under multiplication;
* `mem_harmAll_of_mem_polyAlg`, `polyAlg_topologicalClosure`: so it contains every polynomial in
  the matrix entries, and by the Stone–Weierstrass theorem these are dense in `C(SU(2), ℂ)`.

The proof of the first point uses polarisation (`coeff_mem_of_forall_eval_mem`): if a polynomial
family lies in a subspace, so do its coefficients.
-/

open Polynomial Matrix
open scoped ComplexConjugate

namespace SOnMCMC

/-! ### Polarisation -/

/-- **Polarisation.** If every value `P(τ)`, `τ ∈ ℂ`, of a polynomial with coefficients in a
`ℂ`-algebra lies in a subspace `W`, then every coefficient of `P` lies in `W`. -/
theorem coeff_mem_of_forall_eval_mem {V : Type*} [CommRing V] [Algebra ℂ V] (W : Submodule ℂ V)
    (P : Polynomial V) (h : ∀ τ : ℂ, P.eval (algebraMap ℂ V τ) ∈ W) (i : ℕ) : P.coeff i ∈ W := by
  by_contra hni
  obtain ⟨φ, hφ, hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hni inferInstance
  have hker : ∀ w ∈ W, φ w = 0 := by
    intro w hw
    have : φ w ∈ W.map φ := Submodule.mem_map_of_mem hw
    rw [hW] at this
    simpa using this
  set Q : Polynomial ℂ := ∑ j ∈ P.support, monomial j (φ (P.coeff j)) with hQ
  have hev : ∀ τ : ℂ, Q.eval τ = 0 := by
    intro τ
    have h1 := hker _ (h τ)
    rw [Polynomial.eval_eq_sum, Polynomial.sum, map_sum] at h1
    rw [hQ, Polynomial.eval_finsetSum, ← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul,
      smul_eq_mul, mul_comm]
  have hQ0 : Q = 0 := Polynomial.funext (by simpa using hev)
  have hci : Q.coeff i = φ (P.coeff i) := by
    rw [hQ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hi
    · rfl
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero]
  rw [hQ0, Polynomial.coeff_zero] at hci
  exact hφ hci.symm

/-- The linear coefficient of a polynomial is the value of its derivative at `0`. -/
theorem coeff_one_eq_derivative_eval {V : Type*} [CommRing V] (P : Polynomial V) :
    P.coeff 1 = (derivative P).eval 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

/-! ### The eigenfunction spaces -/

/-- The span of the functions `x ↦ (uᵀ x v)^k` on `SU(2)`. -/
def harm (k : ℕ) : Submodule ℂ (SU2 → ℂ) :=
  Submodule.span ℂ (Set.range fun uv : (Fin 2 → ℂ) × (Fin 2 → ℂ) => lin uv.1 uv.2 ^ k)

theorem lin_pow_mem (u v : Fin 2 → ℂ) (k : ℕ) : lin u v ^ k ∈ harm k :=
  Submodule.subset_span ⟨(u, v), rfl⟩

theorem natCast_mul_eq_smul (m : ℕ) (F : SU2 → ℂ) : ((m : ℕ) : SU2 → ℂ) * F = (m : ℂ) • F := by
  funext x
  simp

/-- First polarisation: `ℓ_{u',v} · ℓ_{u,v}^k ∈ harm (k+1)`. -/
theorem lin_mul_lin_pow_mem (u u' v : Fin 2 → ℂ) (k : ℕ) :
    lin u' v * lin u v ^ k ∈ harm (k + 1) := by
  set P : Polynomial (SU2 → ℂ) := (C (lin u v) + X * C (lin u' v)) ^ (k + 1) with hP
  have hev : ∀ τ : ℂ, P.eval (algebraMap ℂ (SU2 → ℂ) τ) ∈ harm (k + 1) := by
    intro τ
    have : P.eval (algebraMap ℂ (SU2 → ℂ) τ) = lin (u + τ • u') v ^ (k + 1) := by
      rw [hP, eval_pow, eval_add, eval_C, eval_mul, eval_X, eval_C, lin_add_left,
        lin_smul_left, Algebra.smul_def]
    rw [this]
    exact lin_pow_mem _ _ _
  have h1 := coeff_mem_of_forall_eval_mem _ P hev 1
  have hc : P.coeff 1 = ((k + 1 : ℕ) : ℂ) • (lin u' v * lin u v ^ k) := by
    rw [coeff_one_eq_derivative_eval, hP, ← natCast_mul_eq_smul]
    simp [derivative_pow]
    ring
  rw [hc] at h1
  exact (Submodule.smul_mem_iff _ (by exact_mod_cast Nat.succ_ne_zero k)).mp h1

/-- Second polarisation. -/
theorem polar_two (u u' v v' : Fin 2 → ℂ) (k : ℕ) :
    ((k + 1 : ℕ) : ℂ) • (lin u v ^ k * lin u v' * lin u' v) + lin u v ^ (k + 1) * lin u' v'
      ∈ harm (k + 2) := by
  set P : Polynomial (SU2 → ℂ) :=
    (C (lin u v) + X * C (lin u v')) ^ (k + 1) * (C (lin u' v) + X * C (lin u' v')) with hP
  have hev : ∀ τ : ℂ, P.eval (algebraMap ℂ (SU2 → ℂ) τ) ∈ harm (k + 2) := by
    intro τ
    have : P.eval (algebraMap ℂ (SU2 → ℂ) τ)
        = lin u' (v + τ • v') * lin u (v + τ • v') ^ (k + 1) := by
      rw [hP, eval_mul, eval_pow, eval_add, eval_C, eval_mul, eval_X, eval_C, eval_add, eval_C,
        eval_mul, eval_X, eval_C, lin_add_right, lin_smul_right, lin_add_right, lin_smul_right,
        Algebra.smul_def, Algebra.smul_def, mul_comm]
    rw [this]
    exact lin_mul_lin_pow_mem u u' (v + τ • v') (k + 1)
  have h1 := coeff_mem_of_forall_eval_mem _ P hev 1
  have hc : P.coeff 1
      = ((k + 1 : ℕ) : ℂ) • (lin u v ^ k * lin u v' * lin u' v)
        + lin u v ^ (k + 1) * lin u' v' := by
    rw [coeff_one_eq_derivative_eval, hP, ← natCast_mul_eq_smul]
    simp [derivative_pow]
    ring
  rw [hc] at h1
  exact h1

/-- The Cauchy–Binet identity on `SU(2)`, where the determinant is `1`. -/
theorem lin_mul_lin_sub (u u' v v' : Fin 2 → ℂ) (x : SU2) :
    lin u' v' x * lin u v x - lin u v' x * lin u' v x
      = (u 0 * u' 1 - u 1 * u' 0) * (v 0 * v' 1 - v 1 * v' 0) := by
  simp only [lin_apply]
  linear_combination ((u 0 * u' 1 - u 1 * u' 0) * (v 0 * v' 1 - v 1 * v' 0)) * SU2.det_eq x

/-- **Multiplication by a linear form** maps `harm (k+1)` into `harm (k+2) ⊔ harm k`. -/
theorem lin_mul_lin_pow_succ_mem (u v u' v' : Fin 2 → ℂ) (k : ℕ) :
    lin u' v' * lin u v ^ (k + 1) ∈ harm (k + 2) ⊔ harm k := by
  have h2 := polar_two u u' v v' k
  have hid : ((k + 2 : ℕ) : ℂ) • (lin u' v' * lin u v ^ (k + 1))
      = (((k + 1 : ℕ) : ℂ) • (lin u v ^ k * lin u v' * lin u' v)
          + lin u v ^ (k + 1) * lin u' v')
        + (((k + 1 : ℕ) : ℂ) * ((u 0 * u' 1 - u 1 * u' 0) * (v 0 * v' 1 - v 1 * v' 0)))
          • lin u v ^ k := by
    funext x
    have h3 := lin_mul_lin_sub u u' v v' x
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, smul_eq_mul]
    push_cast
    linear_combination (((k : ℂ) + 1) * lin u v x ^ k) * h3
  have hmem : ((k + 2 : ℕ) : ℂ) • (lin u' v' * lin u v ^ (k + 1)) ∈ harm (k + 2) ⊔ harm k := by
    rw [hid]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h2)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (lin_pow_mem u v k)))
  exact (Submodule.smul_mem_iff _ (by exact_mod_cast Nat.succ_ne_zero (k + 1))).mp hmem

/-! ### The algebra of all eigenfunctions -/

/-- The sum of all the spaces `harm k`. -/
def harmAll : Submodule ℂ (SU2 → ℂ) := ⨆ k, harm k

theorem harm_le_harmAll (k : ℕ) : harm k ≤ harmAll := le_iSup harm k

theorem one_mem_harmAll : (1 : SU2 → ℂ) ∈ harmAll :=
  harm_le_harmAll 0 (by simpa using lin_pow_mem 0 0 0)

theorem lin_mem_harmAll (u v : Fin 2 → ℂ) : lin u v ∈ harmAll :=
  harm_le_harmAll 1 (by simpa using lin_pow_mem u v 1)

theorem lin_mul_mem_harmAll (u' v' : Fin 2 → ℂ) {F : SU2 → ℂ} (hF : F ∈ harmAll) :
    lin u' v' * F ∈ harmAll := by
  refine Submodule.iSup_induction harm (motive := fun F => lin u' v' * F ∈ harmAll) hF ?_ ?_ ?_
  · intro k F hF
    refine Submodule.span_induction (p := fun F _ => lin u' v' * F ∈ harmAll) ?_ ?_ ?_ ?_ hF
    · rintro _ ⟨⟨u, v⟩, rfl⟩
      cases k with
      | zero =>
        simp only [pow_zero, mul_one]
        exact lin_mem_harmAll u' v'
      | succ k =>
        exact (sup_le (harm_le_harmAll _) (harm_le_harmAll _))
          (lin_mul_lin_pow_succ_mem u v u' v' k)
    · simp
    · intro a b _ _ ha hb
      rw [mul_add]
      exact add_mem ha hb
    · intro c a _ ha
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c ha
  · simp
  · intro a b ha hb
    rw [mul_add]
    exact add_mem ha hb

theorem lin_pow_mul_mem_harmAll (u v : Fin 2 → ℂ) (k : ℕ) {H : SU2 → ℂ} (hH : H ∈ harmAll) :
    lin u v ^ k * H ∈ harmAll := by
  induction k with
  | zero => simpa using hH
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact lin_mul_mem_harmAll u v ih

/-- **`harmAll` is closed under multiplication.** -/
theorem mul_mem_harmAll {F H : SU2 → ℂ} (hF : F ∈ harmAll) (hH : H ∈ harmAll) :
    F * H ∈ harmAll := by
  refine Submodule.iSup_induction harm (motive := fun F => F * H ∈ harmAll) hF ?_ ?_ ?_
  · intro k F hF
    refine Submodule.span_induction (p := fun F _ => F * H ∈ harmAll) ?_ ?_ ?_ ?_ hF
    · rintro _ ⟨⟨u, v⟩, rfl⟩
      exact lin_pow_mul_mem_harmAll u v k hH
    · simp
    · intro a b _ _ ha hb
      rw [add_mul]
      exact add_mem ha hb
    · intro c a _ ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c ha
  · simp
  · intro a b ha hb
    rw [add_mul]
    exact add_mem ha hb

/-! ### Regularity, parity and conjugation -/

theorem continuous_of_mem_harm {k : ℕ} {F : SU2 → ℂ} (hF : F ∈ harm k) : Continuous F := by
  refine Submodule.span_induction (p := fun F _ => Continuous F) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨⟨u, v⟩, rfl⟩
    exact (continuous_lin u v).pow k
  · exact continuous_const
  · intro a b _ _ ha hb
    exact ha.add hb
  · intro c a _ ha
    exact ha.const_smul c

theorem continuous_of_mem_harmAll {F : SU2 → ℂ} (hF : F ∈ harmAll) : Continuous F := by
  refine Submodule.iSup_induction harm (motive := fun F => Continuous F) hF ?_ ?_ ?_
  · intro k F hF
    exact continuous_of_mem_harm hF
  · exact continuous_const
  · intro a b ha hb
    exact ha.add hb

/-- The central element `-1` of `SU(2)`. -/
def negOne : SU2 := SU2.mk' (-1) 0 (by simp)

theorem lin_negOne_mul (u v : Fin 2 → ℂ) (x : SU2) : lin u v (negOne * x) = -lin u v x := by
  rw [lin_mul, lin_apply, lin_apply]
  simp [negOne, vecMul, dotProduct, Fin.sum_univ_two]
  ring

/-- Elements of `harm k` have parity `(-1)^k`. -/
theorem harm_parity {k : ℕ} {F : SU2 → ℂ} (hF : F ∈ harm k) (x : SU2) :
    F (negOne * x) = (-1) ^ k * F x := by
  refine Submodule.span_induction (p := fun F _ => F (negOne * x) = (-1) ^ k * F x)
    ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨⟨u, v⟩, rfl⟩
    show lin u v (negOne * x) ^ k = (-1) ^ k * lin u v x ^ k
    rw [lin_negOne_mul, neg_pow]
  · simp
  · intro a b _ _ ha hb
    simp only [Pi.add_apply, ha, hb]
    ring
  · intro c a _ ha
    simp only [Pi.smul_apply, ha, smul_eq_mul]
    ring

/-- The complex conjugate of a linear form is a linear form. -/
theorem conj_lin (u v : Fin 2 → ℂ) (x : SU2) :
    conj (lin u v x) = lin ![conj (u 1), -conj (u 0)] ![conj (v 1), -conj (v 0)] x := by
  simp only [lin_apply, map_add, map_mul, SU2.coe_11 x, SU2.coe_10 x, map_neg,
    Complex.conj_conj, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `harm k` is closed under complex conjugation. -/
theorem conj_mem_harm {k : ℕ} {F : SU2 → ℂ} (hF : F ∈ harm k) :
    (fun x => conj (F x)) ∈ harm k := by
  refine Submodule.span_induction (p := fun F _ => (fun x => conj (F x)) ∈ harm k)
    ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨⟨u, v⟩, rfl⟩
    have : (fun x => conj ((lin u v ^ k) x))
        = lin ![conj (u 1), -conj (u 0)] ![conj (v 1), -conj (v 0)] ^ k := by
      funext x
      simp only [Pi.pow_apply, map_pow, conj_lin]
    rw [this]
    exact lin_pow_mem _ _ _
  · have : (fun x : SU2 => conj ((0 : SU2 → ℂ) x)) = 0 := by
      funext x
      simp
    rw [this]
    exact zero_mem _
  · intro a b _ _ ha hb
    have : (fun x => conj ((a + b) x)) = (fun x => conj (a x)) + fun x => conj (b x) := by
      funext x
      simp
    rw [this]
    exact add_mem ha hb
  · intro c a _ ha
    have : (fun x => conj ((c • a) x)) = conj c • fun x => conj (a x) := by
      funext x
      simp
    rw [this]
    exact Submodule.smul_mem _ _ ha

theorem conj_mem_harmAll {F : SU2 → ℂ} (hF : F ∈ harmAll) : (fun x => conj (F x)) ∈ harmAll := by
  refine Submodule.iSup_induction harm (motive := fun F => (fun x => conj (F x)) ∈ harmAll)
    hF ?_ ?_ ?_
  · intro k F hF
    exact harm_le_harmAll k (conj_mem_harm hF)
  · have : (fun x : SU2 => conj ((0 : SU2 → ℂ) x)) = 0 := by
      funext x
      simp
    rw [this]
    exact zero_mem _
  · intro a b ha hb
    have : (fun x => conj ((a + b) x)) = (fun x => conj (a x)) + fun x => conj (b x) := by
      funext x
      simp
    rw [this]
    exact add_mem ha hb

/-! ### Density -/

/-- The coordinate functions of `SU(2)` as continuous maps. -/
def coordC (i j : Fin 2) : C(SU2, ℂ) :=
  ⟨fun x => (x : Matrix (Fin 2) (Fin 2) ℂ) i j, continuous_subtype_val.matrix_elem i j⟩

/-- The star-subalgebra of `C(SU(2), ℂ)` generated by the matrix entries. -/
noncomputable def polyAlg : StarSubalgebra ℂ C(SU2, ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range fun ij : Fin 2 × Fin 2 => coordC ij.1 ij.2)

/-- **Every polynomial in the matrix entries is a sum of eigenfunctions.** -/
theorem mem_harmAll_of_mem_polyAlg {f : C(SU2, ℂ)} (hf : f ∈ polyAlg) :
    (f : SU2 → ℂ) ∈ harmAll := by
  unfold polyAlg at hf
  induction hf using StarAlgebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hf
    have : ((coordC i j : C(SU2, ℂ)) : SU2 → ℂ) = lin (Pi.single i 1) (Pi.single j 1) := by
      funext x
      exact (lin_single i j x).symm
    rw [this]
    exact lin_mem_harmAll _ _
  | algebraMap c =>
    have : ((algebraMap ℂ C(SU2, ℂ) c : C(SU2, ℂ)) : SU2 → ℂ) = c • (1 : SU2 → ℂ) := by
      funext x
      simp
    rw [this]
    exact Submodule.smul_mem _ _ one_mem_harmAll
  | add f g _ _ hf hg => exact add_mem hf hg
  | mul f g _ _ hf hg => exact mul_mem_harmAll hf hg
  | star f _ hf => exact conj_mem_harmAll hf

theorem polyAlg_separatesPoints : polyAlg.SeparatesPoints := by
  intro x y hxy
  have : ∃ i j, (x : Matrix (Fin 2) (Fin 2) ℂ) i j ≠ (y : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    by_contra h
    push Not at h
    exact hxy (Subtype.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := this
  exact ⟨_, ⟨coordC i j, StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩, rfl⟩, hij⟩

/-- **Density.** Polynomials in the matrix entries are dense in `C(SU(2), ℂ)`. -/
theorem polyAlg_topologicalClosure : polyAlg.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    polyAlg_separatesPoints

/-- Every continuous function on `SU(2)` is uniformly approximated by sums of eigenfunctions. -/
theorem exists_harmAll_near (g : C(SU2, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : SU2 → ℂ, p ∈ harmAll ∧ ∀ x, ‖g x - p x‖ ≤ ε := by
  have hg : g ∈ polyAlg.topologicalClosure := by
    rw [polyAlg_topologicalClosure]
    trivial
  have hg' : g ∈ closure (polyAlg : Set C(SU2, ℂ)) := hg
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hg' ε hε
  refine ⟨p, mem_harmAll_of_mem_polyAlg hp, fun x => ?_⟩
  have h1 : ‖(g - p) x‖ ≤ ‖g - p‖ := ContinuousMap.norm_coe_le_norm (g - p) x
  rw [dist_eq_norm] at hdist
  exact h1.trans hdist.le

end SOnMCMC

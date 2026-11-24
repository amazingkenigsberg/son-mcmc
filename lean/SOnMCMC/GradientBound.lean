import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import SOnMCMC.SO2

/-!
# Gradient domination on the maximal torus, and the angle density of the Gaussian step

Paper: Section 7.3 (Lemmas 7.3 and 7.4).

The lower bound on the spectral gap of the Gaussian sampler on `SO(n)` (Theorem 7.5 and
Corollary 7.6 of the paper) is proved by integrating by parts on `SO(n)` and comparing, on the
maximal torus, the gradient of a matrix coefficient with the gradient of the trace.  This file
formalizes the elementary core of that argument.  The Lie-theoretic steps around it (the
Peter–Weyl theorem, the Casimir operator, Haar measure in the coordinates `A ↦ R(A)`) are not
formalized; the paper marks Theorem 7.5 and Corollary 7.6 accordingly.

* `abs_sin_int_mul_le`: `|sin (j t)| ≤ |j| |sin t|` for every integer `j`;
* `hasDerivAt_cosSum_update`, `abs_cosSumDeriv_le`: a nonnegative combination
  `H(θ) = ∑ₐ wₐ ∏ₖ cos (μₐₖ θₖ)` of products of cosines with integer frequencies satisfies
  `|∂H/∂θₖ| ≤ (∑ₐ wₐ μₐₖ²) |sin θₖ|`;
* `gradient_domination`: the pointwise inequality between gradient pairings used in the proof
  of Theorem 7.5;
* `skew_rotMat_mul_skew2`, `det_half_rotMat_add_one`, `pairBlock_mulVec`, `det_pairBlock`: the
  blocks of the linear map `X ↦ skew (t X)` on `so(n)` at a point `t` of the maximal torus, and
  their determinants `cos a`, `(1 + cos a)/2` and `((cos a + cos b)/2)²`;
* `gaussAngleDensity_antitoneOn`: the resulting density of the Gaussian step law, as a function
  of the rotation angles, is nonincreasing on `[0, π]ᵐ` for the coordinatewise order.
-/

open Real Finset Matrix

namespace SOnMCMC

/-! ### `|sin (j t)| ≤ |j| |sin t|` for integers -/

/-- `|sin (j t)| ≤ |j| |sin t|` for every integer `j` (Lemma 4.5 for negative `j`). -/
theorem abs_sin_int_mul_le (j : ℤ) (t : ℝ) : |sin (j * t)| ≤ |(j : ℝ)| * |sin t| := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · simpa using abs_sin_nat_mul_le k t
  · simpa [neg_mul, sin_neg, abs_neg] using abs_sin_nat_mul_le k t

/-! ### Nonnegative combinations of products of cosines -/

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- `∏ₖ cos (μₖ θₖ)`. -/
noncomputable def cosProd (μ : Fin m → ℤ) (θ : Fin m → ℝ) : ℝ :=
  ∏ k, cos (μ k * θ k)

/-- `∑ₐ wₐ ∏ₖ cos (μₐₖ θₖ)`. With `wₐ ≥ 0` this is the form of a matrix coefficient of a
representation of `SO(n)`, averaged over conjugation by `O(n)`, on the maximal torus. -/
noncomputable def cosSum (w : ι → ℝ) (μ : ι → Fin m → ℤ) (θ : Fin m → ℝ) : ℝ :=
  ∑ a, w a * cosProd (μ a) θ

/-- The partial derivative of `cosSum w μ` in the variable `θₖ`. -/
noncomputable def cosSumDeriv (w : ι → ℝ) (μ : ι → Fin m → ℤ) (θ : Fin m → ℝ) (k : Fin m) :
    ℝ :=
  ∑ a, w a * (-(μ a k * sin (μ a k * θ k)) * ∏ l ∈ univ.erase k, cos (μ a l * θ l))

theorem cosProd_update (μ : Fin m → ℤ) (θ : Fin m → ℝ) (k : Fin m) (s : ℝ) :
    cosProd μ (Function.update θ k s) = cos (μ k * s) * ∏ l ∈ univ.erase k, cos (μ l * θ l) := by
  unfold cosProd
  rw [← Finset.mul_prod_erase univ _ (mem_univ k), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hl)]

/-- `cosSumDeriv w μ θ k` is the derivative of `cosSum w μ` in the variable `θₖ`. -/
theorem hasDerivAt_cosSum_update (w : ι → ℝ) (μ : ι → Fin m → ℤ) (θ : Fin m → ℝ)
    (k : Fin m) :
    HasDerivAt (fun s => cosSum w μ (Function.update θ k s)) (cosSumDeriv w μ θ k) (θ k) := by
  have h : (fun s => cosSum w μ (Function.update θ k s)) =
      fun s => ∑ a, w a * (cos (μ a k * s) * ∏ l ∈ univ.erase k, cos (μ a l * θ l)) := by
    funext s
    simp only [cosSum, cosProd_update]
  rw [h, cosSumDeriv]
  refine HasDerivAt.fun_sum fun a _ => ?_
  have h0 : HasDerivAt (fun s : ℝ => (μ a k : ℝ) * s) (μ a k : ℝ) (θ k) := by
    simpa using (hasDerivAt_id (θ k)).const_mul (μ a k : ℝ)
  have h1 : HasDerivAt (fun s => cos (μ a k * s)) (-sin (μ a k * θ k) * μ a k) (θ k) :=
    h0.cos
  exact ((h1.mul_const (∏ l ∈ univ.erase k, cos (μ a l * θ l))).const_mul (w a)).congr_deriv
    (by ring)

/-- **Gradient bound** (Lemma 7.3(a)). For `wₐ ≥ 0`,
`|∂ₖ ∑ₐ wₐ ∏ₗ cos (μₐₗ θₗ)| ≤ (∑ₐ wₐ μₐₖ²) |sin θₖ|`. -/
theorem abs_cosSumDeriv_le {w : ι → ℝ} (hw : ∀ a, 0 ≤ w a) (μ : ι → Fin m → ℤ)
    (θ : Fin m → ℝ) (k : Fin m) :
    |cosSumDeriv w μ θ k| ≤ (∑ a, w a * (μ a k : ℝ) ^ 2) * |sin (θ k)| := by
  rw [cosSumDeriv, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have hP : |∏ l ∈ univ.erase k, cos (μ a l * θ l)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => abs_cos_le_one _
  have hs := abs_sin_int_mul_le (μ a k) (θ k)
  have h0 : 0 ≤ |(μ a k : ℝ)| := abs_nonneg _
  rw [abs_mul, abs_of_nonneg (hw a), abs_mul, abs_neg, abs_mul]
  calc w a * (|(μ a k : ℝ)| * |sin (μ a k * θ k)| * |∏ l ∈ univ.erase k, cos (μ a l * θ l)|)
      ≤ w a * (|(μ a k : ℝ)| * (|(μ a k : ℝ)| * |sin (θ k)|) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left hs h0) hP (abs_nonneg _) (by positivity))
          (hw a)
    _ = w a * (μ a k : ℝ) ^ 2 * |sin (θ k)| := by rw [← sq_abs (μ a k : ℝ)]; ring

/-- If `pₖ sin θₖ ≤ 0` and `|qₖ| ≤ C |sin θₖ|` for every `k`, then
`|∑ₖ pₖ qₖ| ≤ C ∑ₖ (-pₖ sin θₖ)`. -/
theorem abs_sum_mul_le_of_sin (p q θ : Fin m → ℝ) {C : ℝ}
    (hp : ∀ k, p k * sin (θ k) ≤ 0) (hq : ∀ k, |q k| ≤ C * |sin (θ k)|) :
    |∑ k, p k * q k| ≤ C * ∑ k, -(p k * sin (θ k)) := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have h1 : |p k| * |sin (θ k)| = -(p k * sin (θ k)) := by
    rw [← abs_mul, abs_of_nonpos (hp k)]
  rw [abs_mul]
  calc |p k| * |q k| ≤ |p k| * (C * |sin (θ k)|) :=
        mul_le_mul_of_nonneg_left (hq k) (abs_nonneg _)
    _ = C * -(p k * sin (θ k)) := by rw [← h1]; ring

/-- **Gradient domination** (Lemma 7.3(b)), the pointwise inequality behind the paper's main
theorem for general `n` (that theorem itself is not formalized).  Let
`d = n(n-1)/2` and `c > 0`.  If `pₖ sin θₖ ≤ 0` (the density decreases with each angle) and
`|qₖ| ≤ (c/d) |sin θₖ|` (Lemma 7.3(a) for a matrix coefficient with Casimir eigenvalue `c`), then
`|∑ₖ pₖ qₖ| / c ≤ (∑ₖ pₖ · (-(2/n) sin θₖ)) / (n - 1)`; the right side is the same pairing for
`tr R / n`, whose Casimir eigenvalue is `n - 1`. -/
theorem gradient_domination {n : ℕ} (hn : 2 ≤ n) (p q θ : Fin m → ℝ) {c : ℝ} (hc : 0 < c)
    (hp : ∀ k, p k * sin (θ k) ≤ 0)
    (hq : ∀ k, |q k| ≤ c / (n * (n - 1) / 2) * |sin (θ k)|) :
    |∑ k, p k * q k| / c ≤ (∑ k, p k * (-(2 / n) * sin (θ k))) / (n - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have h := abs_sum_mul_le_of_sin p q θ hp hq
  set T := ∑ k, -(p k * sin (θ k)) with hT
  have e : (∑ k, p k * (-(2 / n) * sin (θ k))) = 2 / n * T := by
    rw [hT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, div_le_div_iff₀ hc hn1]
  have hd : c / (n * (n - 1) / 2) * T = c * (2 / n * T) / (n - 1) := by
    field_simp
  rw [hd] at h
  calc |∑ k, p k * q k| * (n - 1) ≤ c * (2 / n * T) / (n - 1) * (n - 1) :=
        mul_le_mul_of_nonneg_right h hn1.le
    _ = 2 / n * T * c := by field_simp

/-! ### The Jacobian of `R ↦ skew R` at a point of the torus

At `t = diag(R_{θ₁}, …, R_{θₘ} [, 1])` the map `X ↦ skew (t X) = (t X + X tᵀ)/2` preserves the
decomposition of `so(n)` into the planes `ℝ J_k`, the `2 × 2` blocks `M_{kl}` (`k < l`) and, for
odd `n`, the columns `N_k`.  It acts on them by the maps below. -/

/-- On `ℝ J`: `(R_a J + J R_aᵀ)/2 = cos a · J`. -/
theorem skew_rotMat_mul_skew2 (a : ℝ) :
    (1 / 2 : ℝ) • (rotMat a * skew2 1 + skew2 1 * (rotMat a).transpose) = cos a • skew2 1 := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [rotMat, skew2] <;> ring

/-- On a column `N_k` (odd `n`): `v ↦ (R_a v + v)/2` has determinant `(1 + cos a)/2`. -/
theorem det_half_rotMat_add_one (a : ℝ) :
    ((1 / 2 : ℝ) • (rotMat a + 1)).det = (1 + cos a) / 2 := by
  rw [Matrix.det_fin_two]
  simp [rotMat]
  nlinarith [sin_sq_add_cos_sq a]

/-- The matrix of `M ↦ (R_a M + M R_bᵀ)/2` on `2 × 2` real matrices, in the basis
`E₁₁, E₁₂, E₂₁, E₂₂`. -/
noncomputable def pairBlock (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(cos a + cos b) / 2, -sin b / 2, -sin a / 2, 0;
     sin b / 2, (cos a + cos b) / 2, 0, -sin a / 2;
     sin a / 2, 0, (cos a + cos b) / 2, -sin b / 2;
     0, sin a / 2, sin b / 2, (cos a + cos b) / 2]

/-- `pairBlock a b` is the matrix of `M ↦ (R_a M + M R_bᵀ)/2`. -/
theorem pairBlock_mulVec (a b : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    pairBlock a b *ᵥ ![M 0 0, M 0 1, M 1 0, M 1 1] =
      ![((1 / 2 : ℝ) • (rotMat a * M + M * (rotMat b).transpose)) 0 0,
        ((1 / 2 : ℝ) • (rotMat a * M + M * (rotMat b).transpose)) 0 1,
        ((1 / 2 : ℝ) • (rotMat a * M + M * (rotMat b).transpose)) 1 0,
        ((1 / 2 : ℝ) • (rotMat a * M + M * (rotMat b).transpose)) 1 1] := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.smul_apply, Matrix.add_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, smul_eq_mul]
  fin_cases i <;> simp [pairBlock, rotMat] <;> ring

/-- On a block `M_{kl}`: `M ↦ (R_a M + M R_bᵀ)/2` has determinant `((cos a + cos b)/2)²`. -/
theorem det_pairBlock (a b : ℝ) : (pairBlock a b).det = ((cos a + cos b) / 2) ^ 2 := by
  simp [pairBlock, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination
    ((4 * cos a * cos b + 4 * cos b ^ 2 + (sin a ^ 2 + cos a ^ 2 - 1) -
        (sin b ^ 2 + cos b ^ 2 - 1)) / 16) * sin_sq_add_cos_sq a +
      ((4 * cos a * cos b + 4 * cos a ^ 2 + (sin b ^ 2 + cos b ^ 2 - 1) -
        (sin a ^ 2 + cos a ^ 2 - 1)) / 16) * sin_sq_add_cos_sq b

/-! ### The angle density of the Gaussian step law -/

/-- The density of the Gaussian step law with respect to Haar measure, up to a constant factor,
as a function of the cosines `cₖ = cos θₖ` of the rotation angles (Lemma 7.4):
`exp(-∑ₖ (1 - cₖ²)/(2v)) · ∏ₖ cₖ · ∏_{k<l} ((cₖ + c_l)/2)² · [∏ₖ (1 + cₖ)/2 if n is odd]`,
where `v = σ²`. -/
noncomputable def gaussCosDensity (odd : Bool) (v : ℝ) (c : Fin m → ℝ) : ℝ :=
  exp (-(∑ k, (1 - c k ^ 2)) / (2 * v)) * (∏ k, c k) *
    (∏ k, ∏ l, if k < l then ((c k + c l) / 2) ^ 2 else 1) *
    (if odd then ∏ k, (1 + c k) / 2 else 1)

/-- The density of the Gaussian step law as a function of the rotation angles: it is
`gaussCosDensity` of the cosines when all angles are in `[-π/2, π/2]` (modulo `2π`), and `0`
otherwise. -/
noncomputable def gaussAngleDensity (odd : Bool) (v : ℝ) (θ : Fin m → ℝ) : ℝ :=
  if ∀ k, 0 ≤ cos (θ k) then gaussCosDensity odd v (fun k => cos (θ k)) else 0

private theorem pairFactor_nonneg (c : Fin m → ℝ) (k l : Fin m) :
    0 ≤ (if k < l then ((c k + c l) / 2) ^ 2 else 1 : ℝ) := by
  split_ifs <;> positivity

theorem gaussCosDensity_nonneg (odd : Bool) (v : ℝ) {c : Fin m → ℝ} (hc : ∀ k, 0 ≤ c k) :
    0 ≤ gaussCosDensity odd v c := by
  unfold gaussCosDensity
  have h1 : 0 ≤ ∏ k, c k := Finset.prod_nonneg fun k _ => hc k
  have h2 : 0 ≤ ∏ k, ∏ l, (if k < l then ((c k + c l) / 2) ^ 2 else 1 : ℝ) :=
    Finset.prod_nonneg fun k _ => Finset.prod_nonneg fun l _ => pairFactor_nonneg c k l
  have h3 : 0 ≤ (if odd then ∏ k, (1 + c k) / 2 else 1 : ℝ) := by
    split_ifs
    · exact Finset.prod_nonneg fun k _ => by linarith [hc k]
    · norm_num
  positivity

/-- On the nonnegative orthant the density is nondecreasing in each cosine. -/
theorem gaussCosDensity_mono (odd : Bool) {v : ℝ} (hv : 0 ≤ v) {c c' : Fin m → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hcc : c ≤ c') :
    gaussCosDensity odd v c ≤ gaussCosDensity odd v c' := by
  have hc' : ∀ k, 0 ≤ c' k := fun k => (hc k).trans (hcc k)
  unfold gaussCosDensity
  have hE : exp (-(∑ k, (1 - c k ^ 2)) / (2 * v)) ≤ exp (-(∑ k, (1 - c' k ^ 2)) / (2 * v)) := by
    refine exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ (by linarith))
    refine neg_le_neg (Finset.sum_le_sum fun k _ => ?_)
    have := pow_le_pow_left₀ (hc k) (hcc k) 2
    linarith
  have hP : ∏ k, c k ≤ ∏ k, c' k :=
    Finset.prod_le_prod (fun k _ => hc k) fun k _ => hcc k
  have hQ : ∏ k, ∏ l, (if k < l then ((c k + c l) / 2) ^ 2 else 1 : ℝ) ≤
      ∏ k, ∏ l, (if k < l then ((c' k + c' l) / 2) ^ 2 else 1 : ℝ) := by
    refine Finset.prod_le_prod (fun k _ => Finset.prod_nonneg fun l _ =>
      pairFactor_nonneg c k l) fun k _ => ?_
    refine Finset.prod_le_prod (fun l _ => pairFactor_nonneg c k l) fun l _ => ?_
    split_ifs
    · exact pow_le_pow_left₀ (by linarith [hc k, hc l]) (by linarith [hcc k, hcc l]) 2
    · exact le_rfl
  have hO : (if odd then ∏ k, (1 + c k) / 2 else 1 : ℝ) ≤
      (if odd then ∏ k, (1 + c' k) / 2 else 1 : ℝ) := by
    split_ifs
    · exact Finset.prod_le_prod (fun k _ => by linarith [hc k]) fun k _ => by linarith [hcc k]
    · exact le_rfl
  have hP0 : 0 ≤ ∏ k, c k := Finset.prod_nonneg fun k _ => hc k
  have hQ0 : 0 ≤ ∏ k, ∏ l, (if k < l then ((c k + c l) / 2) ^ 2 else 1 : ℝ) :=
    Finset.prod_nonneg fun k _ => Finset.prod_nonneg fun l _ => pairFactor_nonneg c k l
  have hO0 : 0 ≤ (if odd then ∏ k, (1 + c k) / 2 else 1 : ℝ) := by
    split_ifs
    · exact Finset.prod_nonneg fun k _ => by linarith [hc k]
    · norm_num
  have hQ0' : 0 ≤ ∏ k, ∏ l, (if k < l then ((c' k + c' l) / 2) ^ 2 else 1 : ℝ) :=
    Finset.prod_nonneg fun k _ => Finset.prod_nonneg fun l _ => pairFactor_nonneg c' k l
  have hP0' : 0 ≤ ∏ k, c' k := Finset.prod_nonneg fun k _ => hc' k
  have hE0 := (exp_pos (-(∑ k, (1 - c k ^ 2)) / (2 * v))).le
  have hE0' := (exp_pos (-(∑ k, (1 - c' k ^ 2)) / (2 * v))).le
  exact mul_le_mul (mul_le_mul (mul_le_mul hE hP hP0 hE0') hQ hQ0 (mul_nonneg hE0' hP0')) hO hO0
    (mul_nonneg (mul_nonneg hE0' hP0') hQ0')

theorem gaussAngleDensity_nonneg (odd : Bool) (v : ℝ) (θ : Fin m → ℝ) :
    0 ≤ gaussAngleDensity odd v θ := by
  unfold gaussAngleDensity
  split_ifs with h
  · exact gaussCosDensity_nonneg odd v h
  · exact le_rfl

/-- **The Gaussian step law is angle-monotone** (Lemma 7.4(b)): its density, as a function of
the rotation angles, is nonincreasing on `[0, π]ᵐ` for the coordinatewise order. -/
theorem gaussAngleDensity_antitoneOn (odd : Bool) {v : ℝ} (hv : 0 ≤ v) :
    AntitoneOn (gaussAngleDensity (m := m) odd v) (Set.Icc 0 fun _ => π) := by
  intro θ hθ θ' hθ' hle
  have hcos : ∀ k, cos (θ' k) ≤ cos (θ k) := fun k =>
    cos_le_cos_of_nonneg_of_le_pi (hθ.1 k) (hθ'.2 k) (hle k)
  by_cases h' : ∀ k, 0 ≤ cos (θ' k)
  · have h : ∀ k, 0 ≤ cos (θ k) := fun k => (h' k).trans (hcos k)
    simp only [gaussAngleDensity, h, h', implies_true, ↓reduceIte]
    exact gaussCosDensity_mono odd hv h' hcos
  · simp only [gaussAngleDensity, h', ↓reduceIte]
    exact gaussAngleDensity_nonneg odd v θ

end SOnMCMC

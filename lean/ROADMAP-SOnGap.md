# Roadmap: formalizing Theorem 7.5 / Corollary 7.6 (exact spectral gap on SO(n))

Goal (Lean): for `2 ≤ n` and every variance `v`,

* `gaussSO_isSpectralGap : IsSpectralGap (haarSO n) (gaussSOStep n v) (1 - stdEig (gaussSOStep n v))`
* `gaussSO_isLeast_contraction : IsLeast {ρ | 0 ≤ ρ ∧ L2ContractionBound (haarSO n) (gaussSOStep n v) ρ} (stdEig _)`

No Peter–Weyl, no Haar measure in coordinates, no matrix exponential. The proof works in the
coordinates `x ∈ Pairs n → ℝ` of the Gaussian proposal `A = √v · skewOf x`.

## Mathematical route (differs from the paper's Section 7.3 proof in the bookkeeping only)

1. **Finite-dimensional substitute for Peter–Weyl.** `V_k` = polynomial functions of degree ≤ k in
   the entries, restricted to `SO(n)`, as a subspace of `L²(haar)`. It is finite-dimensional and
   invariant under right translations `ρ(Q)` and under the left-invariant derivatives
   `D_X g (x) = Dg̃(x)[x X]`. The Casimir `Ω = -Σ_p D_{J_p}²` is self-adjoint (Green's formula along
   Cayley curves `Cay(sX)`, using only right invariance of Haar measure), so
   `V_k = ⊕_c W_c` orthogonally (Mathlib spectral theorem). `P_ν` preserves each `W_c` (it commutes
   with `Ω`), and `W_0` consists of constants. Polynomials are dense in `L²` (Stone–Weierstrass), so
   it suffices to prove `|⟨g, P_ν g⟩| ≤ λ ‖g‖²` (and the operator-norm version) for `g ∈ W_c`, `c > 0`.
2. **Matrix coefficient.** `h(M) = ∫ conj(g x) g(xM) dx` (a polynomial in `M`), `h̃` its average over
   conjugation by `SO(n)` and the reflection `r`. Then `⟨g, P_ν g⟩ = ∫ h̃ dν`, `Δh̃ = -c h̃`, and
   `h̃ ∘ t = cosSum w μ` with `w ≥ 0`, `Σ w_μ μ_k² = c/d` (explicit torus weights via the monomials in
   `z = M_{i,2k-1} + i M_{i,2k}`; Casimir averaging `∫ ρ(Q) D_{E_k}² ρ(Q)⁻¹ dQ = -Ω/d`).
3. **Integration by parts in proposal space.** On `B = {x : 1 + A² ≻ 0}` the step `R(x)` is `C¹`
   (inverse function theorem for `M ↦ skew M + ½(MᵀM - 1)`), with `dR = R · L_R⁻¹`, where
   `L_R(X) = skew(R X)`. The fields `X̂ = L_R(X)` satisfy `X̂(u ∘ R) = (D_X u) ∘ R` and
   `div X̂ = X̂ (log det L_R)` (trace identity, `tr ad_X = 0`). With a cutoff `η(det(1+A²)/δ)` and
   dominated convergence (majorant `1/λ_min(sym R)`, integrable by the layer-cake formula):
   `∫_B φ H = (1/c) ∫_B Σ_p (X̂_p H)(X̂_p f̂) / det L_R`, `f̂ = φ · det L_R`, and the same for `tr/n`.
4. **Pointwise comparison.** At `R = P t(θ) Pᵀ` (normal form of rotations): gradients of
   `O(n)`-class functions live on the torus (sign-flip conjugation), the pairing is
   `Σ_k ∂_k U ∂_k W`, `f ∘ t = gaussAngleDensity` (block determinant of `L_{t(θ)}`), and
   `gradient_domination` (Lemma 7.3(b), already formalized) closes the estimate.

## Work packages (files under `SOnMCMC/`)

| # | File | Content | Status |
|---|---|---|---|
| 1 | `NormalForm.lean` | every `R ∈ SO(n)` is `P t(θ) Pᵀ` with `P ∈ SO(n)` (`exists_torusMat_conj`) | **done** (885 lines, in the build, no warnings) |
| 2 | `SkewCalculus.lean` | basis `J_p`, `L_M`, coercivity, trace identity, `det L_{t(θ)}` blocks | todo |
| 3 | `StepSmooth.lean` | `R(x)` is differentiable on `B`, `dR = R L_R⁻¹`, `det L_R > 0` | todo |
| 4 | `LieDeriv.lean` | `D_X u M = Du(M)[M X]`, chain rule along `R`, class functions on the torus | todo |
| 5 | `PolySpace.lean` | `V_k ⊂ L²`, `ρ`, `D_X`, `Ω` self-adjoint, eigen-decomposition, `W_0` = constants | todo |
| 6 | `TorusWeights.lean` | weight vectors, `h̃ ∘ t = cosSum`, Casimir averaging | todo |
| 7 | `ProposalIBP.lean` | cutoff IBP on `B`, integrability, per-eigenvector inequality | todo |
| 8 | `SOnGap.lean` | density of polynomials, `L²` bound, Poincaré, spectral gap, least contraction | todo |

Already done: `GradientBound.lean` (Lemmas 7.3, 7.4: gradient bound, Jacobian blocks, monotone
angle density).

## Status and next step (paused 2026-11-23)

* Done: package 1. `torusMat N θ` takes angles `θ : ℕ → ℝ` (avoids `Fin (N/2)` casts); peel lemmas
  `torusMat_succ_succ`, `torusMat_castSucc`, block determinants `det_of_firstBlock`,
  `det_of_lastBlock`, orthonormal-family helpers (`IsOrthonormalFamily`, `colMat`,
  `eq_sum_of_orthonormal`), and `hasTorusForm` (strong induction on eigenvectors of `R + Rᵀ`).
* Next: package 3 (`StepSmooth.lean`). Plan: apply `HasStrictFDerivAt.localInverse` to
  `Φ M = skewPart M + ½ (Mᵀ M - 1)` at `R = principalStep A₀` with `symPart R ≻ 0`.
  `DΦ_R Y = skewPart Y + ½ (Rᵀ Y + Yᵀ R)` is injective: `skewPart Y = 0`, then
  `tr(Y (P Y + Y P)) > 0` unless `Y = 0` (`P = symPart R`; the commutator term with `skewPart R` has
  trace 0). For skew `A` near `A₀` the local inverse is orthogonal with skew part `A` and positive
  definite symmetric part, so it equals `principalStep A` (`eq_principalStep`).
  Then `DR(x)[y] = R Z` with `Z` skew, `skewPart (R Z) = √v · skewOf y`.
* The paper (Theorem 7.5, Corollary 7.6) still marks the main result as not formalized. Remark 7.7
  and Table 1 of the paper mention `NormalForm.lean`; no numbered statement cites it yet.

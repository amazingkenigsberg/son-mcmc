import SOnMCMC.CompactWalk

/-!
# Conjugacy-class measures and `L²` extension arguments

Paper: Section 6.3.

General tools used for `SU(2)` and `SO(3)`:

* `IsConjInvariant ν`: `ν` is invariant under `q ↦ g q g⁻¹` for every `g` in the group;
  `classMeasure m q` is the image of `m` under `g ↦ g q g⁻¹`, the uniform measure on the
  conjugacy class of `q` when `m` is Haar measure;
* `markovOp_congr_ae`: the Markov operator respects almost-everywhere equality;
* `integral_norm_sq_markovOp_le_of_approx`: an `L²` bound that holds on a dense set of functions
  holds for every `L²` function;
* `integral_norm_sq_sum_of_orthogonal`: Pythagoras for finite orthogonal families;
* `norm_integral_sq_le_weighted`: a weighted Cauchy–Schwarz inequality.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace SOnMCMC

section ClassMeasure

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- A measure on a group is *conjugation invariant* if it is preserved by `q ↦ g q g⁻¹` for
every `g`. -/
def IsConjInvariant (ν : Measure G) : Prop := ∀ g : G, ν.map (fun q => g * q * g⁻¹) = ν

/-- The image of `m` under `g ↦ g q g⁻¹`: for Haar measure `m`, the uniform probability measure
on the conjugacy class of `q`. -/
noncomputable def classMeasure (m : Measure G) (q : G) : Measure G :=
  m.map (fun g => g * q * g⁻¹)

theorem measurable_conj_left (q : G) : Measurable fun g : G => g * q * g⁻¹ :=
  (measurable_id.mul_const q).mul measurable_inv

omit [MeasurableInv G] in
theorem measurable_conj_right (g : G) : Measurable fun q : G => g * q * g⁻¹ :=
  (measurable_id.const_mul g).mul_const g⁻¹

instance (m : Measure G) [IsProbabilityMeasure m] (q : G) :
    IsProbabilityMeasure (classMeasure m q) :=
  Measure.isProbabilityMeasure_map (measurable_conj_left q).aemeasurable

/-- A class measure is conjugation invariant. -/
theorem classMeasure_isConjInvariant (m : Measure G) [m.IsMulLeftInvariant] (q : G) :
    IsConjInvariant (classMeasure m q) := by
  intro h
  have hcomp : (fun r : G => h * r * h⁻¹) ∘ (fun g : G => g * q * g⁻¹)
      = (fun g : G => g * q * g⁻¹) ∘ fun g : G => h * g := by
    funext g
    simp [mul_assoc]
  rw [classMeasure, Measure.map_map (measurable_conj_right h) (measurable_conj_left q), hcomp,
    ← Measure.map_map (measurable_conj_left q) (measurable_const_mul h), map_mul_left_eq_self]

/-- If `q⁻¹` is conjugate to `q`, the class measure of `q` is invariant under inversion. -/
theorem classMeasure_map_inv (m : Measure G) [m.IsMulRightInvariant] {q w : G}
    (hw : w * q * w⁻¹ = q⁻¹) : (classMeasure m q).map Inv.inv = classMeasure m q := by
  have hcomp : Inv.inv ∘ (fun g : G => g * q * g⁻¹)
      = (fun g : G => g * q * g⁻¹) ∘ fun g : G => g * w := by
    funext g
    simp only [Function.comp, mul_inv_rev, inv_inv]
    rw [← hw]
    simp [mul_assoc]
  rw [classMeasure, Measure.map_map measurable_inv (measurable_conj_left q), hcomp,
    ← Measure.map_map (measurable_conj_left q) (measurable_mul_const w), map_mul_right_eq_self]

/-- Integrals against a class measure. -/
theorem integral_classMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : Measure G) (q : G) {F : G → E} (hF : AEStronglyMeasurable F (classMeasure m q)) :
    ∫ r, F r ∂(classMeasure m q) = ∫ g, F (g * q * g⁻¹) ∂m :=
  integral_map (measurable_conj_left q).aemeasurable hF

end ClassMeasure

section AE

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Markov operator respects almost-everywhere equality.** -/
theorem markovOp_congr_ae (m ν : Measure G) [SFinite m] [SFinite ν] [m.IsMulRightInvariant]
    {F H : G → E} (h : F =ᵐ[m] H) : markovOp ν F =ᵐ[m] markovOp ν H := by
  have hT := measurePreserving_mul_prod m ν
  have h1 : (fun z : G × G => F z.1) =ᵐ[m.prod ν] fun z => H z.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp h
  have h2 : (fun z : G × G => F (z.1 * z.2)) =ᵐ[m.prod ν] fun z => H (z.1 * z.2) :=
    hT.quasiMeasurePreserving.ae_eq_comp h1
  have h3 := Measure.ae_ae_of_ae_prod h2
  filter_upwards [h3] with x hx
  exact integral_congr_ae hx

/-- The Markov operator is additive on integrable functions, almost everywhere. -/
theorem markovOp_sub_ae (m ν : Measure G) [SFinite m] [IsFiniteMeasure ν]
    [m.IsMulRightInvariant] {F H : G → E} (hF : Integrable F m) (hH : Integrable H m) :
    markovOp ν (fun x => F x - H x) =ᵐ[m] fun x => markovOp ν F x - markovOp ν H x := by
  filter_upwards [(integrable_comp_mul m ν hF).prod_right_ae,
    (integrable_comp_mul m ν hH).prod_right_ae] with x h1 h2
  simp only [markovOp]
  exact integral_sub h1 h2

end AE

section Extension

variable {α : Type*} [MeasurableSpace α]

theorem sq_norm_add_le (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + 1 / δ) * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖a‖ * ‖b‖ ≤ δ * ‖a‖ ^ 2 + 1 / δ * ‖b‖ ^ 2 := by
    have h4 : 0 ≤ 1 / δ * (δ * ‖a‖ - ‖b‖) ^ 2 := by positivity
    have h5 : 1 / δ * (δ * ‖a‖ - ‖b‖) ^ 2
        = δ * ‖a‖ ^ 2 - 2 * ‖a‖ * ‖b‖ + 1 / δ * ‖b‖ ^ 2 := by
      field_simp
      ring
    linarith
  nlinarith

/-- `∫ ‖u + w‖² ≤ (1 + δ) ∫ ‖u‖² + (1 + 1/δ) ∫ ‖w‖²`. -/
theorem integral_sq_norm_add_le (μ : Measure α) {u w : α → ℂ} (hu : MemLp u 2 μ)
    (hw : MemLp w 2 μ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, ‖u x + w x‖ ^ 2 ∂μ
      ≤ (1 + δ) * ∫ x, ‖u x‖ ^ 2 ∂μ + (1 + 1 / δ) * ∫ x, ‖w x‖ ^ 2 ∂μ := by
  have hu2 : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hw2 : Integrable (fun x => ‖w x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
  have huw : Integrable (fun x => ‖u x + w x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hu.add hw).aestronglyMeasurable).mp (hu.add hw)
  calc ∫ x, ‖u x + w x‖ ^ 2 ∂μ
      ≤ ∫ x, ((1 + δ) * ‖u x‖ ^ 2 + (1 + 1 / δ) * ‖w x‖ ^ 2) ∂μ :=
        integral_mono huw ((hu2.const_mul _).add (hw2.const_mul _))
          fun x => sq_norm_add_le (u x) (w x) hδ
    _ = _ := by
        rw [integral_add (hu2.const_mul _) (hw2.const_mul _), integral_const_mul,
          integral_const_mul]

end Extension

section Approx

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

/-- **Extension by density.** If an `L²` function `f` can be approximated in `L²` by functions
`p` for which `‖P p‖₂ ≤ ρ ‖p‖₂`, then `‖P f‖₂ ≤ ρ ‖f‖₂`. -/
theorem integral_norm_sq_markovOp_le_of_approx (m ν : Measure G) [IsProbabilityMeasure m]
    [IsProbabilityMeasure ν] [m.IsMulRightInvariant] {ρ : ℝ} {f : G → ℂ} (hf : MemLp f 2 m)
    (h : ∀ ε > 0, ∃ p : G → ℂ, MemLp p 2 m ∧ ∫ x, ‖f x - p x‖ ^ 2 ∂m ≤ ε ∧
      ∫ x, ‖markovOp ν p x‖ ^ 2 ∂m ≤ ρ ^ 2 * ∫ x, ‖p x‖ ^ 2 ∂m) :
    ∫ x, ‖markovOp ν f x‖ ^ 2 ∂m ≤ ρ ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂m := by
  set A := ∫ x, ‖markovOp ν f x‖ ^ 2 ∂m with hA
  set B := ρ ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂m with hB
  have hI0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂m := integral_nonneg fun x => by positivity
  have hB0 : 0 ≤ B := mul_nonneg (sq_nonneg ρ) hI0
  set K := 3 * B + 2 * (1 + 2 * ρ ^ 2) with hK
  have hKpos : 0 < K := by positivity
  -- the estimate for a given δ ∈ (0, 1]
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → A ≤ B + δ * K := by
    intro δ hδ hδ1
    obtain ⟨p, hp, hfp, hPp⟩ := h (δ ^ 2) (by positivity)
    have hfp_mem : MemLp (fun x => f x - p x) 2 m := hf.sub hp
    have hpf_mem : MemLp (fun x => p x - f x) 2 m := hp.sub hf
    have hPp_mem := memLp_markovOp m ν hp
    have hPd := memLp_markovOp_and_le m ν hfp_mem
    -- `P f = P p + P (f - p)` almost everywhere
    have hae : markovOp ν f =ᵐ[m] fun x => markovOp ν p x + markovOp ν (fun x => f x - p x) x := by
      have h1 := markovOp_sub_ae m ν (hf.integrable one_le_two) (hp.integrable one_le_two)
      filter_upwards [h1] with x hx
      rw [hx]
      ring
    have hA1 : A = ∫ x, ‖markovOp ν p x + markovOp ν (fun x => f x - p x) x‖ ^ 2 ∂m :=
      integral_congr_ae (hae.mono fun x hx => by
        show ‖markovOp ν f x‖ ^ 2 = _
        rw [hx])
    have hA2 := integral_sq_norm_add_le m hPp_mem hPd.1 hδ
    have hpdecomp : ∫ x, ‖p x‖ ^ 2 ∂m
        = ∫ x, ‖f x + (p x - f x)‖ ^ 2 ∂m := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp
    have hp2 := integral_sq_norm_add_le m hf hpf_mem hδ
    have hsymm : ∫ x, ‖p x - f x‖ ^ 2 ∂m = ∫ x, ‖f x - p x‖ ^ 2 ∂m := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [norm_sub_rev]
    rw [← hpdecomp, hsymm] at hp2
    have hd0 : 0 ≤ ∫ x, ‖f x - p x‖ ^ 2 ∂m := integral_nonneg fun x => by positivity
    have hI : ∫ x, ‖p x‖ ^ 2 ∂m ≤ (1 + δ) * ∫ x, ‖f x‖ ^ 2 ∂m + (1 + 1 / δ) * δ ^ 2 := by
      have : (1 + 1 / δ) * ∫ x, ‖f x - p x‖ ^ 2 ∂m ≤ (1 + 1 / δ) * δ ^ 2 :=
        mul_le_mul_of_nonneg_left hfp (by positivity)
      linarith
    have hPdle : ∫ x, ‖markovOp ν (fun x => f x - p x) x‖ ^ 2 ∂m ≤ δ ^ 2 := hPd.2.trans hfp
    -- assemble
    have e1 : (1 + 1 / δ) * δ ^ 2 = δ ^ 2 + δ := by
      field_simp
    have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    have step1 : A ≤ (1 + δ) * (ρ ^ 2 * ∫ x, ‖p x‖ ^ 2 ∂m) + (1 + 1 / δ) * δ ^ 2 := by
      rw [hA1]
      have h1 : (1 + δ) * ∫ x, ‖markovOp ν p x‖ ^ 2 ∂m
          ≤ (1 + δ) * (ρ ^ 2 * ∫ x, ‖p x‖ ^ 2 ∂m) :=
        mul_le_mul_of_nonneg_left hPp (by positivity)
      have h2 : (1 + 1 / δ) * ∫ x, ‖markovOp ν (fun x => f x - p x) x‖ ^ 2 ∂m
          ≤ (1 + 1 / δ) * δ ^ 2 := mul_le_mul_of_nonneg_left hPdle (by positivity)
      linarith
    have step2 : ρ ^ 2 * ∫ x, ‖p x‖ ^ 2 ∂m ≤ (1 + δ) * B + ρ ^ 2 * (δ ^ 2 + δ) := by
      have := mul_le_mul_of_nonneg_left hI hρ2
      rw [e1] at this
      rw [hB]
      linarith [this]
    rw [e1] at step1
    have step3 : (1 + δ) * (ρ ^ 2 * ∫ x, ‖p x‖ ^ 2 ∂m)
        ≤ (1 + δ) * ((1 + δ) * B + ρ ^ 2 * (δ ^ 2 + δ)) :=
      mul_le_mul_of_nonneg_left step2 (by positivity)
    have hδ2 : δ ^ 2 ≤ δ := by nlinarith
    rw [hK]
    nlinarith [mul_nonneg hB0 hδ.le, mul_nonneg hρ2 hδ.le,
      mul_nonneg (mul_nonneg hρ2 hδ.le) hδ.le, mul_nonneg (mul_nonneg hB0 hδ.le) hδ.le]
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hδpos : 0 < min 1 (η / K) := lt_min one_pos (div_pos hη hKpos)
  have h1 := key (min 1 (η / K)) hδpos (min_le_left _ _)
  have h2 : min 1 (η / K) * K ≤ η := by
    calc min 1 (η / K) * K ≤ η / K * K := mul_le_mul_of_nonneg_right (min_le_right _ _) hKpos.le
      _ = η := div_mul_cancel₀ η hKpos.ne'
  linarith

end Approx

section Orthogonal

variable {α : Type*} [MeasurableSpace α]

/-- **Pythagoras.** For a finite family of pairwise orthogonal functions,
`∫ |∑ cᵢ hᵢ|² = ∑ |cᵢ|² ∫ |hᵢ|²`. -/
theorem integral_norm_sq_sum_of_orthogonal (μ : Measure α) {ι : Type*} (s : Finset ι)
    (h : ι → α → ℂ) (c : ι → ℂ)
    (hint : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun x => h i x * conj (h j x)) μ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ x, h i x * conj (h j x) ∂μ = 0) :
    ∫ x, ‖∑ i ∈ s, c i * h i x‖ ^ 2 ∂μ = ∑ i ∈ s, ‖c i‖ ^ 2 * ∫ x, ‖h i x‖ ^ 2 ∂μ := by
  have hsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpt : ∀ x, ((‖∑ i ∈ s, c i * h i x‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s, (c i * conj (c j)) * (h i x * conj (h j x)) := by
    intro x
    rw [hsq, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  have hC : ((∫ x, ‖∑ i ∈ s, c i * h i x‖ ^ 2 ∂μ : ℝ) : ℂ)
      = ((∑ i ∈ s, ‖c i‖ ^ 2 * ∫ x, ‖h i x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [hpt]
    rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj =>
      (hint i hi j hj).const_mul _]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finsetSum _ fun j hj => (hint i hi j hj).const_mul _]
    rw [Finset.sum_eq_single i]
    · rw [integral_const_mul, ← integral_complex_ofReal]
      congr 1
      · rw [← hsq]
        push_cast
        ring
      · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact (hsq (h i x)).symm
    · intro j hj hji
      rw [integral_const_mul, horth i hi j hj (Ne.symm hji), mul_zero]
    · intro hi'
      exact absurd hi hi'
  exact_mod_cast hC

end Orthogonal

end SOnMCMC

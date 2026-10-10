-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderCutoffMoments
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Space-time integrability and normalization of small-positive moments. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- Square integrability on a finite product cylinder supplies its time moment,
almost every spatial moment, and the exact conversion to the extended power
moment used in norm iteration. -/
theorem integrable_shifted_small_power_outer_moment {T α : Type*}
    [MeasurableSpace T] [MeasurableSpace α] (τ : Measure T) (μ : Measure α)
    [IsFiniteMeasure τ] [IsFiniteMeasure μ] {u : T × α → ℝ} {c p : ℝ}
    (hc : 0 < c) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hu : MemLp u 2 (τ.prod μ)) (hu0 : ∀ᵐ z ∂τ.prod μ, 0 ≤ u z) :
    Integrable (fun t => ∫ x, (u (t, x) + c) ^ p ∂μ) τ ∧
      (∀ᵐ t ∂τ, Integrable (fun x => (u (t, x) + c) ^ p) μ) ∧
      ENNReal.ofReal (∫ t, ∫ x, (u (t, x) + c) ^ p ∂μ ∂τ) =
        ∫⁻ z, ‖u z + c‖ₑ ^ p ∂τ.prod μ := by
  have hi := integrable_shifted_small_power_of_memLp_two hc hp hp1 hu hu0
  refine ⟨hi.integral_prod_left, hi.prod_right_ae, ?_⟩
  have hpos : ∀ᵐ z ∂τ.prod μ, 0 ≤ (u z + c) ^ p := by
    filter_upwards [hu0] with z hz
    exact Real.rpow_nonneg (add_nonneg hz hc.le) p
  rw [← integral_prod _ hi, ofReal_integral_eq_lintegral_ofReal hi hpos]
  apply lintegral_congr_ae
  filter_upwards [hu0] with z hz
  rw [← Real.enorm_of_nonneg (Real.rpow_nonneg (add_nonneg hz hc.le) p),
    Real.enorm_rpow_of_nonneg (add_nonneg hz hc.le) hp]

/-- Local square integrability and the spatial cutoff bounds supply time
integrability of both literal cutoff moments and their comparison with the
outer moment. All support and cutoff-gradient hypotheses are explicit. -/
theorem integrable_reverse_holder_spacetime_cutoff_moments {T α ι : Type*}
    [MeasurableSpace T] [MeasurableSpace α] [Fintype ι]
    (τ : Measure T) (μ : Measure α) [IsFiniteMeasure τ] [SFinite μ]
    {V : Set α} (hV : MeasurableSet V) [IsFiniteMeasure (μ.restrict V)]
    {u : T × α → ℝ} {c p L : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hu : MemLp u 2 (τ.prod (μ.restrict V)))
    (hu0 : ∀ᵐ z ∂τ.prod (μ.restrict V), 0 ≤ u z)
    {η : α → ℝ} {d : ι → α → ℝ}
    (hη : AEStronglyMeasurable η μ) (hηunit : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hηsupport : ∀ x ∉ V, η x = 0) (hd : ∀ i, MemLp (d i) 2 μ)
    (hdsupport : ∀ i x, x ∉ V → d i x = 0)
    (hdL : ∀ᵐ x ∂μ, coordinateNormSq (fun i => d i x) ≤ L) :
    let m := fun t => ∫ x in V, (u (t, x) + c) ^ p ∂μ
    let E := fun t => ∫ x, η x ^ 2 * (u (t, x) + c) ^ p ∂μ
    let K := fun t => ∫ x, (u (t, x) + c) ^ p * coordinateNormSq (fun i => d i x) ∂μ
    Integrable m τ ∧ Integrable E τ ∧ Integrable K τ ∧
      ∀ᵐ t ∂τ, 0 ≤ m t ∧ 0 ≤ E t ∧ E t ≤ m t ∧ K t ≤ L * m t := by
  dsimp only
  have hi := integrable_shifted_small_power_of_memLp_two hc hp hp1 hu hu0
  have hm := hi.integral_prod_left
  have hmeasure : τ.prod (μ.restrict V) = (τ.prod μ).restrict (univ ×ˢ V) := by
    simpa only [Measure.restrict_univ] using Measure.prod_restrict (μ := τ) (ν := μ) univ V
  have hfi : IntegrableOn (fun z => (u z + c) ^ p) (univ ×ˢ V) (τ.prod μ) := by
    unfold IntegrableOn
    rw [← hmeasure]
    exact hi
  have hpos : ∀ᵐ z ∂τ.prod (μ.restrict V), 0 ≤ (u z + c) ^ p := by
    filter_upwards [hu0] with z hz
    exact Real.rpow_nonneg (add_nonneg hz hc.le) p
  have hpos' : ∀ᵐ z ∂(τ.prod μ).restrict (univ ×ˢ V), 0 ≤ (u z + c) ^ p := by
    rwa [← hmeasure]
  have hηs : ∀ z : T × α, z ∉ univ ×ˢ V → η z.2 = 0 :=
    fun z hz => hηsupport z.2 (fun hx => hz ⟨mem_univ _, hx⟩)
  have hds : ∀ i (z : T × α), z ∉ univ ×ˢ V → d i z.2 = 0 :=
    fun i z hz => hdsupport i z.2 (fun hx => hz ⟨mem_univ _, hx⟩)
  obtain ⟨hEi, hKi, _, _, _⟩ := reverse_holder_cutoff_moment_bounds
    (MeasurableSet.univ.prod hV) hfi hpos' hη.comp_snd (fun z => hηunit z.2)
      hηs (fun i => (hd i).comp_snd τ) hds (Measure.quasiMeasurePreserving_snd.ae hdL)
  refine ⟨hm, hEi.integral_prod_left, hKi.integral_prod_left, ?_⟩
  filter_upwards [hi.prod_right_ae, Measure.ae_ae_of_ae_prod hpos] with t ht hpt
  obtain ⟨_, _, hE0, hEbound, hKbound⟩ := reverse_holder_cutoff_moment_bounds
    hV ht hpt hη hηunit hηsupport hd hdsupport hdL
  exact ⟨integral_nonneg_of_ae hpt, hE0, hEbound, hKbound⟩

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TransportLp
public import RothschildStein.H3.TaylorWeightedPower
public import RothschildStein.H3.GroupTransport
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- Averaging right translations of the homogeneous group
 is an Lp contraction for every finite p ≥ 1. -/
theorem group_average_memLp_and_norm_le {α : Type*} [MeasurableSpace α]
    {n : ℕ} (G : HomogeneousGroup n)
    (μ : Measure α) [IsProbabilityMeasure μ] (E : α → (Fin n → ℝ))
    (hE : Measurable E) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : (Fin n → ℝ) → ℝ} (hf : StronglyMeasurable f) (hfp : MemLp f p volume) :
    MemLp (fun x => ∫ t, f (G.mul x (E t)) ∂μ) p volume ∧
      eLpNorm (fun x => ∫ t, f (G.mul x (E t)) ∂μ) p volume ≤ eLpNorm f p volume := by
  have hjoint : Measurable (fun z : α × (Fin n → ℝ) => G.mul z.2 (E z.1)) := by
    exact group_right_transport_measurable G hE
  have hpres : ∀ t, MeasurePreserving (fun x => G.mul x (E t)) volume volume :=
    fun t => RothschildStein.G2.measurePreserving_rightTranslation G (E t)
  exact transport_average_memLp_and_norm_le μ volume
    (fun z => G.mul z.2 (E z.1)) hjoint hpres hp hpt hf hfp

/-- The actual Taylor weighted remainder has Lp norm at most
 one half of the spatial norm of the transported second derivative. -/
theorem group_taylor_remainder_memLp_and_norm_le {n : ℕ} (G : HomogeneousGroup n)
    (E : ℝ → (Fin n → ℝ)) (hE : Measurable E)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : (Fin n → ℝ) → ℝ} (hf : StronglyMeasurable f) (hfp : MemLp f p volume) :
    MemLp (fun x => ∫ t in (0 : ℝ)..1, (1-t)*f (G.mul x (E t))) p volume ∧
      eLpNorm (fun x => ∫ t in (0 : ℝ)..1, (1-t)*f (G.mul x (E t))) p volume ≤
        ENNReal.ofReal (1/2 : ℝ) * eLpNorm f p volume := by
  let : IsProbabilityMeasure taylorProbability := taylorProbability_isProbability
  obtain ⟨ha,hb⟩ := group_average_memLp_and_norm_le G taylorProbability E hE hp hpt hf hfp
  have he : (fun x => ∫ t in (0 : ℝ)..1, (1-t)*f (G.mul x (E t))) =
      (1/2 : ℝ) • (fun x => ∫ t, f (G.mul x (E t)) ∂taylorProbability) := by
    funext x
    simp only [Pi.smul_apply,smul_eq_mul,integral_taylorProbability]
    ring
  rw [he]
  refine ⟨ha.const_smul (1/2 : ℝ),?_⟩
  rw [eLpNorm_const_smul]
  have hc : ‖(1/2 : ℝ)‖ₑ = ENNReal.ofReal (1/2 : ℝ) := by
    simp only [Real.enorm_eq_ofReal_abs,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [hc]
  gcongr

end RothschildStein.H3

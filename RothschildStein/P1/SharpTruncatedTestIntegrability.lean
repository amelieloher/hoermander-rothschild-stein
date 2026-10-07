-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LocalizedChartGauge
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- Finite tested sharp truncations are genuinely
jointly integrable. Compactness away from the pole supplies the bound;
the canonical representative removes arbitrary diagonal values. -/
theorem integrable_sharpTruncated_tested_representative {lam : ℕ}
    (hF : C.IsLiftedFrame F)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) (d : TypeDecomposition F lam 1 κ)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (f g : TestFunction F.V ℝ (⊤ : ℕ∞)) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      g p.1 * ((if ε < C.localizedInputGauge ν p.1 p.2 then d.measurableKernel p.1 p.2 else 0) * f p.2))
      (volume.prod volume) := by
  classical
  let S := tsupport g ×ˢ tsupport f
  let B := S ∩ (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => ν (C.Θ p.2 p.1)) ⁻¹' Ici ε
  let a := fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
    g p.1 * ((if ε < C.localizedInputGauge ν p.1 p.2 then d.measurableKernel p.1 p.2 else 0) * f p.2)
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  have hS : IsCompact S := g.hasCompactSupport.prod f.hasCompactSupport
  have hSU : S ⊆ C.U ×ˢ C.U := fun p hp =>
    ⟨hVU (g.tsupport_subset hp.1), hVU (f.tsupport_subset hp.2)⟩
  have hθ : ContinuousOn
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => ν (C.Θ p.2 p.1)) S :=
    hν.1.comp_continuousOn ((C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)).continuousOn.mono hSU)
  have hB : IsCompact B := hθ.upperSemicontinuousOn.isCompact_inter_preimage_Ici hS ε
  have hBE : B ⊆ (((F.V : Set _) ×ˢ (F.V : Set _)) ∩ {p | p.1 ≠ p.2}) := by
    intro p hp
    refine ⟨⟨g.tsupport_subset hp.1.1, f.tsupport_subset hp.1.2⟩, ?_⟩
    intro he
    have hz : C.Θ p.2 p.1 = 0 := by
      rw [he]
      exact (C.theta_eq_zero_iff (hSU hp.1).2 (hSU hp.1).2).mpr rfl
    have hn := hp.2
    change ε ≤ ν (C.Θ p.2 p.1) at hn
    rw [hz, (hν.2.2.1 0).mpr rfl] at hn
    exact (not_le_of_gt hε) hn
  have hc : ContinuousOn (Function.uncurry d.measurableKernel) B := by
    apply ((C.isTypeKernel_continuousOn_joint hF hκ).mono hBE).congr
    intro p hp
    exact d.measurableKernel_eq_off_diagonal p.1 p.2 (hBE hp).2
  have hraw : ContinuousOn
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        g p.1 * (d.measurableKernel p.1 p.2 * f p.2)) B :=
    (g.contDiff.continuous.comp continuous_fst).continuousOn.mul
      (hc.mul (f.contDiff.continuous.comp continuous_snd).continuousOn)
  obtain ⟨M, hm⟩ := hB.exists_bound_of_continuousOn hraw
  have hr := C.measurable_typeDecomposition_kernel F hF.Θ_eq hVU hF.pole_smooth d
  have ha : Measurable a :=
    (g.contDiff.continuous.measurable.comp measurable_fst).mul
      ((Measurable.ite (measurableSet_lt measurable_const (C.measurable_localizedInputGauge hν.1))
        hr measurable_const).mul (f.contDiff.continuous.measurable.comp measurable_snd))
  have hbound : ∀ p ∈ S, ‖a p‖ ≤ max M 0 := by
    intro p hp
    dsimp only [a]
    by_cases ht : ε < C.localizedInputGauge ν p.1 p.2
    · rw [ite_eq_left ht]
      have hb : p ∈ B := by
        refine ⟨hp, ?_⟩
        rw [C.localizedInputGauge_eq ν (hSU hp).1 (hSU hp).2] at ht
        exact ht.le
      exact (hm p hb).trans (le_max_left _ _)
    · rw [ite_eq_right ht, zero_mul, mul_zero, norm_zero]
      exact le_max_right _ _
  have hi : IntegrableOn a S (volume.prod volume) :=
    Measure.integrableOn_of_bounded hS.measure_lt_top.ne ha.aestronglyMeasurable
      ((ae_restrict_mem hS.measurableSet).mono (fun p hp => hbound p hp))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro p hp
  by_contra hs
  have hz : g p.1 = 0 ∨ f p.2 = 0 := by
    by_contra hn
    push Not at hn
    exact hs ⟨subset_tsupport g hn.1, subset_tsupport f hn.2⟩
  apply hp
  rcases hz with hg | hf
  · simp only [a, hg, zero_mul]
  · simp only [a, hf, mul_zero]

end RothschildStein.P1.LiftedChart

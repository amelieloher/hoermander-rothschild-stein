-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SharpTruncatedTestIntegrability
public import RothschildStein.P1.AmbientTruncationLocalization
public import RothschildStein.P1.GaugeChartIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The actual tested sharp row agrees with the
jointly measurable finite-truncation representative. -/
theorem sharp_tested_row_eq_representative {lam : ℕ}
    (hF : C.IsLiftedFrame F)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (d : TypeDecomposition F lam 1 κ)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : Continuous ν)
    (f g : TestFunction F.V ℝ (⊤ : ℕ∞)) (ε : ℝ) (ξ : Fin (n + m) → ℝ) :
    g ξ * (∫ η in {η | ε < ν (C.Θ η ξ)}, κ ξ η * f η) =
      ∫ η, g ξ * ((if ε < C.localizedInputGauge ν ξ η then d.measurableKernel ξ η else 0) * f η) := by
  classical
  let rsSharpRowRepresentativeNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  by_cases hz : g ξ = 0
  · simp only [hz, zero_mul, integral_zero]
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  have hξ : ξ ∈ C.U := hVU (g.tsupport_subset (subset_tsupport g hz))
  let A := C.U ∩ {η | ε < ν (C.Θ η ξ)}
  have hA : MeasurableSet A :=
    ((hν.comp_continuousOn (C.contDiffOn_Θ_fst hξ).continuousOn).isOpen_inter_preimage
      C.isOpen_U isOpen_Ioi).measurableSet
  have hfzero : ∀ η, η ∉ C.U → κ ξ η * f η = 0 := by
    intro η hη
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (hVU (f.tsupport_subset ht))), mul_zero]
  have he : (∫ η in {η | ε < ν (C.Θ η ξ)}, κ ξ η * f η) =
      ∫ η in A, κ ξ η * f η := by
    symm
    simpa only [A, inter_comm] using integral_localizedTruncation (μ := volume)
      (A := {η | ε < ν (C.Θ η ξ)}) C.isOpen_U.measurableSet hfzero
  rw [he, ← integral_indicator hA, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne ξ] with η hηξ
  by_cases hη : η ∈ C.U
  · rw [C.localizedInputGauge_eq ν hξ hη]
    by_cases ht : ε < ν (C.Θ η ξ)
    · rw [indicator_of_mem (show η ∈ A from ⟨hη, ht⟩), ite_eq_left ht,
        d.measurableKernel_eq_off_diagonal ξ η hηξ.symm]
    · rw [indicator_of_notMem (show η ∉ A from fun h => ht h.2), ite_eq_right ht,
        zero_mul, mul_zero]
  · have hf : f η = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hη (hVU (f.tsupport_subset ht)))
    rw [indicator_of_notMem (show η ∉ A from fun h => hη h.1), hf,
      mul_zero, mul_zero, mul_zero]

end RothschildStein.P1.LiftedChart

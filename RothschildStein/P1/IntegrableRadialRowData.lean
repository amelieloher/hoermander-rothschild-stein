-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RadialSharpRowData
public import RothschildStein.P1.IntegrableChartRadialLimit
public import RothschildStein.P1.RadialGaugeCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Absolutely integrable chart rows have both
sharp and radial finite integrability and their common full integral limit. -/
def integrableRadialRowData {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : Integrable f)
    (hs : ∀ η, η ∉ C.U → f η = 0) :
    RadialSharpRowData (fun η => ν (C.Θ η ξ))
      (fun ε η => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) f where
  value := ∫ η, f η
  sharp_integrable := fun _ _ => hf.integrableOn
  radial_integrable := by
    classical
    intro ε _
    let A := fun η => if η ∈ C.U then 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))) else 0
    have hc : ContinuousOn (fun η => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) C.U :=
      continuousOn_const.sub
        (radialCutoffProfile_contDiff.continuous.comp_continuousOn
          (hν.1.comp_continuousOn ((G2.continuous_dilate C.G ε⁻¹).comp_continuousOn
            (C.contDiffOn_Θ_fst hξ).continuousOn)))
    have hm : AEStronglyMeasurable A :=
      (aestronglyMeasurable_indicator_iff C.isOpen_U.measurableSet).mpr
        (hc.aestronglyMeasurable C.isOpen_U.measurableSet)
    have hb : ∀ η, ‖A η‖ ≤ 2 := by
      intro η
      by_cases hη : η ∈ C.U
      · simp only [A, ite_eq_left hη]
        have h := norm_sub_le (1 : ℝ) (radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))
        have hp := radialCutoffProfile_norm_le (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))
        norm_num only [norm_one] at h
        linarith
      · simp only [A, ite_eq_right hη, norm_zero]
        norm_num
    have hi := hf.bdd_mul hm (Eventually.of_forall hb)
    apply hi.congr
    exact Eventually.of_forall (fun η => by
      by_cases hη : η ∈ C.U
      · simp only [A, ite_eq_left hη]
      · simp only [A, ite_eq_right hη, hs η hη, mul_zero])
  sharp_limit := C.tendsto_integrableChart_truncation hξ hν hf hs
  radial_limit := C.tendsto_integrableChart_radialCutoff hξ hν hf hs radialCutoffProfile
    radialCutoffProfile_contDiff.continuous (by norm_num : (0 : ℝ) < 2)
    (fun r hr => radialCutoffProfile_zero hr) (fun u => radialCutoffProfile_norm_le (ν u))

end RothschildStein.P1.LiftedChart

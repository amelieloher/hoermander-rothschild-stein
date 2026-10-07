-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LocalFlatFieldJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Freeze a field at the base point in the
leading ordinary jet, under the source's local smoothness hypotheses. -/
theorem iteratedFDeriv_fieldDerivative_eq_frozen_on {N k : ℕ}
    (Ω : Opens (Fin N → ℝ)) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (u : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ} (hx : x ∈ Ω)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    (hz : ∀ j < k + 1, iteratedFDeriv ℝ j u x = 0) :
    iteratedFDeriv ℝ k (fieldDerivative V u) x =
      iteratedFDeriv ℝ k (fieldDerivative (fun _ => V x) u) x := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ u) Ω := hu.fderiv_of_isOpen Ω.isOpen (by simp)
  have he : fieldDerivative V u - fieldDerivative (fun _ => V x) u =
      fieldDerivative (fun y => V y - V x) u := by
    ext y
    simp [fieldDerivative,map_sub]
  have hz' := iteratedFDeriv_fieldDerivative_zero_of_field_zero_on Ω
    (fun y => V y - V x) u hx (hV.sub contDiffOn_const) hu hz (sub_self _)
  rw [← he] at hz'
  have ha : ContDiffAt ℝ k (fieldDerivative V u) x :=
    ((hd.clm_apply hV).of_le (by simp)).contDiffAt (Ω.isOpen.mem_nhds hx)
  have hb : ContDiffAt ℝ k (fieldDerivative (fun _ => V x) u) x :=
    ((hd.clm_apply contDiffOn_const).of_le (by simp)).contDiffAt (Ω.isOpen.mem_nhds hx)
  rw [iteratedFDeriv_sub_apply ha hb] at hz'
  exact sub_eq_zero.mp hz'

end RothschildStein.L1

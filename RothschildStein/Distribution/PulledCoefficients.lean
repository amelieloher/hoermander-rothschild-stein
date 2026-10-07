-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.FrameExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.Distribution

/-- pulling an arbitrary Euclidean coefficient
family back and pushing it forward restores the original family. -/
theorem push_pulledVectorFields {k N : ℕ}
    (V : Fin (k + 1) → Hormander.F.E₂ N → Hormander.F.E₂ N) :
    Hormander.F.pushVectorFields
      (fun i x => (Hormander.F.coordinateEquiv N).symm (V i (Hormander.F.coordinateEquiv N x))) = V := by
  funext i y
  simp [Hormander.F.pushVectorFields, Hormander.F.pushVectorField]

/-- the pulled compact coefficient patch has
smooth fields on the coordinates `Fin N → ℝ`. -/
theorem contDiff_pulledVectorField {N : ℕ}
    (V : Hormander.F.E₂ N → Hormander.F.E₂ N) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (Hormander.F.coordinateEquiv N).symm (V (Hormander.F.coordinateEquiv N x))) :=
  (Hormander.F.coordinateEquiv N).symm.contDiff.comp (hV.comp (Hormander.F.coordinateEquiv N).contDiff)

/-- patched coefficient agreement on the Euclidean
ball gives exact agreement of the pulled fields on `Fin N → ℝ` there. -/
theorem pulledPatch_fields_eqOn {k N : ℕ} (hN : 0 < N)
    (Ω : Set (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (x₀ : Fin N → ℝ)
    (P : Hormander.F.LocalPatch hN (Hormander.F.coordinateEquiv N '' Ω)
      (Hormander.F.pushVectorFields X) (fun y => c ((Hormander.F.coordinateEquiv N).symm y))
      (Hormander.F.coordinateEquiv N x₀)) (i : Fin (k + 1)) :
    EqOn (fun x => (Hormander.F.coordinateEquiv N).symm
      (P.extendedX i (Hormander.F.coordinateEquiv N x))) (X i)
      ((Hormander.F.coordinateEquiv N) ⁻¹' Metric.ball (Hormander.F.coordinateEquiv N x₀) P.radius) := by
  intro x hx
  have he := (P.extendedX_eq_near_ball i).self_of_nhdsSet
    (Hormander.F.coordinateEquiv N x) (subset_closure hx)
  have hp := congrArg (Hormander.F.coordinateEquiv N).symm he
  simpa only [Hormander.F.pushVectorFields, Hormander.F.pushVectorField,
    ContinuousLinearEquiv.symm_apply_apply] using hp

/-- zeroth-order coefficients have the same exact
agreement after pulling back the patch. -/
theorem pulledPatch_multiplier_eqOn {k N : ℕ} (hN : 0 < N)
    (Ω : Set (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (x₀ : Fin N → ℝ)
    (P : Hormander.F.LocalPatch hN (Hormander.F.coordinateEquiv N '' Ω)
      (Hormander.F.pushVectorFields X) (fun y => c ((Hormander.F.coordinateEquiv N).symm y))
      (Hormander.F.coordinateEquiv N x₀)) :
    EqOn (fun x => P.extendedC (Hormander.F.coordinateEquiv N x)) c
      ((Hormander.F.coordinateEquiv N) ⁻¹' Metric.ball (Hormander.F.coordinateEquiv N x₀) P.radius) := by
  intro x hx
  have he := P.extendedC_eq_near_ball.self_of_nhdsSet
    (Hormander.F.coordinateEquiv N x) (subset_closure hx)
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using he

/-- the pulled frame ball is inside the original
open set, as required by every distribution-test restriction. -/
theorem pulledPatch_ball_subset {k N : ℕ} (hN : 0 < N)
    (Ω : Set (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (x₀ : Fin N → ℝ)
    (P : Hormander.F.LocalPatch hN (Hormander.F.coordinateEquiv N '' Ω)
      (Hormander.F.pushVectorFields X) (fun y => c ((Hormander.F.coordinateEquiv N).symm y))
      (Hormander.F.coordinateEquiv N x₀)) :
    (Hormander.F.coordinateEquiv N) ⁻¹' Metric.ball (Hormander.F.coordinateEquiv N x₀) P.radius ⊆ Ω := by
  intro x hx
  obtain ⟨y, hy, he⟩ := P.ball_closure_subset (subset_closure hx)
  have hyx : y = x := (Hormander.F.coordinateEquiv N).injective he
  simpa only [hyx] using hy

end RothschildStein.Distribution

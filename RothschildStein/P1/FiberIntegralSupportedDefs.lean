-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSeminormBound
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- Fiber integration on functions supported in one fixed
compact set, with output supported in its base projection. -/
def fiberIntegralSupportedLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (K : Compacts ((Fin n → ℝ) × (Fin d → ℝ))) :
    ContDiffMapSupportedIn ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤ K →ₗ[ℝ]
      ContDiffMapSupportedIn (Fin n → ℝ) B ⊤ (K.map Prod.fst continuous_fst) where
  toFun φ :=
    { toFun x := ∫ z, φ (x, z)
      contDiff' := contDiff_fiberIntegral φ.contDiff φ.hasCompactSupport
      zero_on_compl' := by
        intro x hx
        change (∫ z, φ (x, z)) = 0
        apply integral_eq_zero_of_ae
        apply Filter.Eventually.of_forall
        intro z
        apply φ.zero_on_compl
        intro hp
        exact hx ⟨(x, z), hp, rfl⟩ }
  map_add' φ ψ := by
    ext x
    exact integral_add (integrable_fiberSection φ.continuous φ.hasCompactSupport x)
      (integrable_fiberSection ψ.continuous ψ.hasCompactSupport x)
  map_smul' c φ := by
    ext x
    exact integral_smul c (fun z => φ (x, z))

/-- All supported-test seminorms have one fixed fiber-volume
bound, independent of the input test and the derivative order. -/
theorem seminorm_fiberIntegralSupportedLM_le {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (K : Compacts ((Fin n → ℝ) × (Fin d → ℝ))) (i : ℕ)
    (φ : ContDiffMapSupportedIn ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤ K) :
    ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) B ⊤
      (K.map Prod.fst continuous_fst) i (fiberIntegralSupportedLM K φ) ≤
      volume.real (Prod.snd '' (K : Set ((Fin n → ℝ) × (Fin d → ℝ)))) *
      ContDiffMapSupportedIn.seminorm ℝ ((Fin n → ℝ) × (Fin d → ℝ)) B ⊤ K i φ := by
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ
    (mul_nonneg ENNReal.toReal_nonneg (apply_nonneg _ _)) i _).mpr
  intro x _
  exact norm_iteratedFDeriv_fiberIntegral_le φ.contDiff φ.hasCompactSupport
    (K.isCompact.image continuous_snd)
    (fun p hp => ⟨p, φ.tsupport_subset hp, rfl⟩) i
    (fun _ => ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ) x

end RothschildStein.P1

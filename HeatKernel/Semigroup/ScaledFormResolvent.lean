-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalFormResolvent
public import HeatKernel.Semigroup.CoerciveFormSolutions

/-! # Resolvents for a positive energy scale

The graph norm makes the scaled form coercive with constant `min 1 scale`.
Lax–Milgram then constructs its unique solution on the same closed energy domain.
-/

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- The mass inner product plus a scaled horizontal energy. -/
def scaledEnergyBilin (scale : ℝ) : energyGraph U X →L[ℝ] energyGraph U X →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSesqForm (𝕜 := ℝ) (E := energyGraph U X) (E' := SpatialL2 U)
    (energyInclusion U X)).comp (energyInclusion U X) +
    scale • (ContinuousLinearMap.toSesqForm (𝕜 := ℝ) (E := energyGraph U X)
      (E' := PiLp 2 (fun _ : Fin q => SpatialL2 U)) (energyGradient U X)).comp (energyGradient U X)

@[simp] theorem scaledEnergyBilin_apply (scale : ℝ) (u v : energyGraph U X) :
    scaledEnergyBilin U X scale u v =
      inner ℝ (energyInclusion U X u) (energyInclusion U X v) +
        scale * horizontalEnergy U X u v := rfl

theorem scaledEnergyBilin_isCoercive (scale : ℝ) (hscale : 0 < scale) :
    IsCoercive (scaledEnergyBilin U X scale) := by
  refine ⟨min 1 scale, lt_min zero_lt_one hscale, ?_⟩
  intro u
  rw [scaledEnergyBilin_apply, real_inner_self_eq_norm_sq]
  have hn := energyGraph_norm_sq_eq U X u
  have hn' := congrArg (fun r : ℝ => min 1 scale * r) hn
  have he := horizontalEnergy_self_nonneg U X u
  have ha := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) scale)
    (sq_nonneg ‖energyInclusion U X u‖)
  have hb := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) scale) he
  nlinarith only [hn', ha, hb]

/-- The energy-domain solution operator at a positive scale. -/
def scaledEnergySolution (scale : ℝ) (hscale : 0 < scale) : SpatialL2 U →L[ℝ] energyGraph U X :=
  coerciveFormSolution (V := energyGraph U X) (H := SpatialL2 U) (B := scaledEnergyBilin U X scale)
    (hB := scaledEnergyBilin_isCoercive U X scale hscale) (j := energyInclusion U X)

theorem scaledEnergySolution_equation (scale : ℝ) (hscale : 0 < scale) (f : SpatialL2 U)
    (v : energyGraph U X) :
    inner ℝ (energyInclusion U X (scaledEnergySolution U X scale hscale f))
      (energyInclusion U X v) +
      scale * horizontalEnergy U X (scaledEnergySolution U X scale hscale f) v =
        inner ℝ f (energyInclusion U X v) := by
  have hc : IsCoercive (scaledEnergyBilin U X scale) :=
    scaledEnergyBilin_isCoercive U X scale hscale
  have he := coerciveFormSolution_equation (V := energyGraph U X) (H := SpatialL2 U)
    (B := scaledEnergyBilin U X scale) (hB := hc)
    (j := energyInclusion U X) (f := f) (v := v)
  rw [scaledEnergyBilin_apply] at he
  exact he

/-- The spatial resolvent at a positive scale. -/
def scaledHorizontalFormResolvent (scale : ℝ) (hscale : 0 < scale) : SpatialL2 U →L[ℝ] SpatialL2 U :=
  (energyInclusion U X).comp (scaledEnergySolution U X scale hscale)

@[simp] theorem scaledHorizontalFormResolvent_apply (scale : ℝ) (hscale : 0 < scale)
    (f : SpatialL2 U) :
    scaledHorizontalFormResolvent U X scale hscale f =
      energyInclusion U X (scaledEnergySolution U X scale hscale f) := rfl

end HeatKernel

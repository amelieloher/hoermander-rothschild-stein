-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransferForward
public import RothschildStein.P1.PaddingNoDriftControlDistance
public import RothschildStein.P1.PaddingControlDistance
public import RothschildStein.P1.PaddingCylinderFiberSetting

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Pullback by the diffusion-padding projection does not increase
the full Hölder norm, with ambient metric domains independent of output sets. -/
theorem holderENorm_paddingNoDrift_pullback_le {q n d : ℕ}
    (ΩA : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (α : ℝ) (hα : 0 ≤ α) (f : (Fin n → ℝ) → ℝ) :
    holderENorm (controlDistance (P2.cylinder ΩA JA : Set (Fin (n + d) → ℝ))
      (paddingNoDriftWeights (d := d) w) (paddingNoDriftVectorFields (d := d) X)) α
      (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) (fun ξ => f (basePoint ξ)) ≤
      holderENorm (controlDistance (ΩA : Set (Fin n → ℝ)) w X) α
        (Ω : Set (Fin n → ℝ)) f := by
  apply P2.holderENorm_comp_le hα (fun _ h => (P2.mem_cylinder.mp h).1)
  intro ξ _ η _
  exact controlDistance_paddingNoDrift_projection_le (padding_cylinder_subset_base ΩA JA) w X ξ η

/-- Pullback by the drift-preserving padding projection does not increase the
full Hölder norm, using the original ambient control distance. -/
theorem holderENorm_paddingDrift_pullback_le {q n d : ℕ}
    (ΩA : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (α : ℝ) (hα : 0 ≤ α) (f : (Fin n → ℝ) → ℝ) :
    holderENorm (controlDistance (P2.cylinder ΩA JA : Set (Fin (n + d) → ℝ))
      (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)) α
      (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) (fun ξ => f (basePoint ξ)) ≤
      holderENorm (controlDistance (ΩA : Set (Fin n → ℝ)) w X) α
        (Ω : Set (Fin n → ℝ)) f := by
  apply P2.holderENorm_comp_le hα (fun _ h => (P2.mem_cylinder.mp h).1)
  intro ξ _ η _
  exact controlDistance_padding_projection_le (padding_cylinder_subset_base ΩA JA) w X ξ η

end RothschildStein.P1

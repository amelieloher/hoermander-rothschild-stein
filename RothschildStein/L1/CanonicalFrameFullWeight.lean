-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialFrameWeightUpgrade
public import RothschildStein.L1.CanonicalFrameFirstWeight
public import RothschildStein.L1.CanonicalBasisBracketWeight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The actual free canonical basis fields have their full assigned
weights, by ordinary jet induction and the radial Euler identity. -/
theorem canonical_frame_full_weight {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (i : Fin (freeDimension a s p)) :
    fullFieldJetClass (ball 0 C.radius) D.weight (-(D.weight i : ℝ))
      (C.coordinateField η i) := by
  let U : Opens (Fin (freeDimension a s p) → ℝ) := ⟨ball 0 C.radius,isOpen_ball⟩
  have h0 : (0 : Fin (freeDimension a s p) → ℝ) ∈ U := mem_ball_self C.radius_pos
  have hY : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (canonicalWordFrame D X k) Ω :=
    fun k => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D k)
  have hZ := fun k => C.coordinateField_contDiffOn hY η hη k
  have hZ0 := fun k => C.basis_values Ω.isOpen hY η hη k
  have hrad := fun u hu => C.radial_identity Ω.isOpen hY η u hη hu
  have hall : ∀ q k, fieldJetClass U D.weight (-(D.weight k : ℝ)) q
      (C.coordinateField η k) := by
    intro q
    induction q with
    | zero =>
      intro k
      exact fieldJetClass_zero_order_of_coordinate_value U D.weight k _ (hZ k) (hZ0 k)
    | succ q ih =>
      cases q with
      | zero =>
        intro k
        exact canonical_frame_first_weight D Ω X hX C η hη k
      | succ q =>
        have hB := canonical_basis_bracket_weight_of_basis_weight D Ω X hX C η hη ih
        have hc := radial_coordinate_bracket_weight_step_of_basis_brackets U h0
          D.weight (C.coordinateField η) ih hZ0 hrad hB
        intro k
        exact radial_frame_weight_upgrade_of_coordinate_brackets U h0 D.weight
          (C.coordinateField η) hZ hrad hc k
  intro q
  exact hall q i
end RothschildStein.L1

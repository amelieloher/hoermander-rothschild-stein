-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialFrameWeightUpgrade
public import RothschildStein.L1.RadialFirstWeight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- Full radial frame weights follow from preservation of the finite
filtration by the actual basis commutators. -/
theorem radial_frame_full_weight_of_bracket_closure {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Z k) Ω)
    (hZ0 : ∀ k, Z k 0 = Pi.single k 1)
    (hrad : ∀ u ∈ Ω, ∑ k, u k • Z k u = u)
    (hclose : ∀ q, (∀ k, fieldJetClass Ω ω (-(ω k : ℝ)) q (Z k)) →
      ∀ i j, fieldJetClass Ω ω (-(ω i : ℝ) - ω j) q
        (VectorField.lieBracket ℝ (Z i) (Z j))) (i : Fin N) :
    fullFieldJetClass Ω ω (-(ω i : ℝ)) (Z i) := by
  have hz : ∀ k, fieldJetClass Ω ω (-(ω k : ℝ)) 0 (Z k) :=
    fun k => fieldJetClass_zero_order_of_coordinate_value Ω ω k _ (hZ k) (hZ0 k)
  have hfirst : ∀ k, fieldJetClass Ω ω (-(ω k : ℝ)) 1 (Z k) := by
    apply fieldJetClass_one_of_radial_bracket_values Ω h0 ω Z hZ hrad hZ0
    intro j l k hk
    exact (hclose 0 hz j l).2 k [] (by simp) (by
      simp only [List.map_nil,List.sum_nil,Nat.cast_zero]
      linarith)
  have hall : ∀ q k, fieldJetClass Ω ω (-(ω k : ℝ)) q (Z k) := by
    intro q
    induction q with
    | zero => exact hz
    | succ q ih =>
      cases q with
      | zero => exact hfirst
      | succ q =>
        have hc := radial_coordinate_bracket_weight_step_of_basis_brackets Ω h0
          ω Z ih hZ0 hrad (hclose (q+1) ih)
        exact radial_frame_weight_upgrade_of_coordinate_brackets Ω h0 ω Z hZ hrad hc
  intro q
  exact hall q i
end RothschildStein.L1

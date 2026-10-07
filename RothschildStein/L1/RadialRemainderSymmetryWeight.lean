-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialBracketRemainderIdentity
public import RothschildStein.L1.RadialRemainderBracketErrors
public import RothschildStein.L1.RadialZeroBracketSum
public import RothschildStein.L1.WeightedFieldAddition
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The radial remainder coordinate commutators are symmetric modulo
strict finite jet weights, using the exact bracket difference premise. -/
theorem radial_remainder_symmetry_weight_of_bracket_difference {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ k, fullFieldJetClass Ω ω (-(ω k : ℝ)) (Z k))
    (hY : ∀ k, fullFieldJetClass Ω ω (-(ω k : ℝ)) (Y k))
    (hY0 : ∀ k, Y k 0 = Pi.single k 1)
    (hradZ : ∀ u ∈ Ω, ∑ k, u k • Z k u = u)
    (hradY : ∀ u ∈ Ω, ∑ k, u k • Y k u = u)
    (hR : ∀ k, fieldJetClass Ω ω (1 - (ω k : ℝ)) q (fun u => Z k u - Y k u))
    (hB : ∀ j i, fieldJetClass Ω ω (1 - (ω i : ℝ) - ω j) q
      (fun u => VectorField.lieBracket ℝ (Z j) (Z i) u -
        VectorField.lieBracket ℝ (Y j) (Y i) u)) (i j : Fin N) :
    fieldJetClass Ω ω (1 - (ω i : ℝ) - ω j) q
      (fun u => VectorField.lieBracket ℝ (fun v => Z j v - Y j v)
        (fun _ => Pi.single i 1) u -
        VectorField.lieBracket ℝ (fun v => Z i v - Y i v)
          (fun _ => Pi.single j 1) u) := by
  let R := fun k u => Z k u - Y k u
  have hs := fieldJetClass_add Ω h0
    (fieldJetClass_add Ω h0 (hB j i)
      (radial_remainder_actual_error_weight Ω h0 ω Z R hZ hR i j))
    (radial_remainder_model_error_weight Ω h0 ω Y R hY hY0 hR i j)
  have hradR : ∀ u ∈ Ω, ∑ k, u k • R k u = 0 := by
    intro u hu
    dsimp only [R]
    simp only [smul_sub,Finset.sum_sub_distrib,hradZ u hu,hradY u hu,sub_self]
  apply fieldJetClass_congr Ω h0 hs
  intro u hu
  have he := radial_bracket_remainder_identity Ω Z Y (fun k => (hZ k 0).1)
    (fun k => (hY k 0).1) hradZ hradY hu i j
  have hz := radial_zero_bracket_sum Ω R (fun k => (hR k).1) hradR hu i j
  change (∑ k, VectorField.lieBracket ℝ (fun _ => Pi.single j 1)
      (fun v => v k • VectorField.lieBracket ℝ (fun _ => Pi.single i 1)
        (fun w => Z k w - Y k w) v) u) = _ at hz
  rw [hz] at he
  exact he
end RothschildStein.L1

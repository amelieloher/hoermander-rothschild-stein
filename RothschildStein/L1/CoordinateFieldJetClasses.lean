-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CoordinateJetClasses
public import RothschildStein.L1.WeightedFieldLocality
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The constant coordinate vector has exactly its assigned negative weight. -/
theorem fieldJetClass_coordinateVector {N p : ℕ} (Ω : Set (Fin N → ℝ))
    (ω : Fin N → ℕ) (i : Fin N) :
    fieldJetClass Ω ω (-(ω i : ℝ)) p (fun _ => (Pi.single i (1 : ℝ) : Fin N → ℝ)) := by
  refine ⟨contDiffOn_const, ?_⟩
  intro j J _ hw
  rw [rsPartial_const]
  by_cases hJ : J = []
  · subst J
    simp only [ite_true]
    have hij : i ≠ j := by
      intro he
      subst j
      have hh : (0 : ℝ) < -(ω i : ℝ) + ω i := by
        simpa only [List.map_nil, List.sum_nil, Nat.cast_zero] using hw
      linarith
    simp only [Pi.single_apply, Ne.symm hij, ite_false]
  · simp only [hJ, ite_false]

/-- The zero field belongs to every smooth finite jet class. -/
theorem fieldJetClass_zero {N p : ℕ} (Ω : Set (Fin N → ℝ))
    (ω : Fin N → ℕ) (a : ℝ) : fieldJetClass Ω ω a p (fun _ => (0 : Fin N → ℝ)) :=
  ⟨contDiffOn_const, fun j => (scalarJetClass_zero Ω ω (a + ω j)).2⟩

/-- Subtracting the matching coordinate vector gives a circle field class. -/
theorem circleFieldJetClass_coordinate_difference {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (ω : Fin N → ℕ) (i : Fin N)
    (Z : (Fin N → ℝ) → (Fin N → ℝ)) (hZ : fieldJetClass Ω ω (-(ω i : ℝ)) p Z)
    (hZ0 : Z 0 = Pi.single i 1) :
    circleFieldJetClass Ω ω (-(ω i : ℝ)) p (fun u => Z u - Pi.single i 1) :=
  ⟨fieldJetClass_sub Ω h0 hZ (fieldJetClass_coordinateVector Ω ω i), by change Z 0 - Pi.single i 1 = 0; rw [hZ0, sub_self]⟩

/-- The standard value at zero starts the frame weight induction at degree zero. -/
theorem fieldJetClass_zero_order_of_coordinate_value {N : ℕ} (Ω : Set (Fin N → ℝ))
    (ω : Fin N → ℕ) (i : Fin N) (Z : (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (hZ0 : Z 0 = Pi.single i 1) :
    fieldJetClass Ω ω (-(ω i : ℝ)) 0 Z := by
  refine ⟨hZ, ?_⟩
  intro j J hJ hw
  have he : J = [] := List.length_eq_zero_iff.mp (by omega)
  subst J
  change Z 0 j = 0
  rw [hZ0]
  exact (fieldJetClass_coordinateVector (p := 0) Ω ω i).2 j [] (by simp) hw
end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalBasisBracketExpansion
public import RothschildStein.L1.RadialFirstWeight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- The first ordinary weight order for the actual canonical frame,
using its proved radial identity and homogeneous commutator coefficients. -/
theorem canonical_frame_first_weight {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (i : Fin (freeDimension a s p)) :
    fieldJetClass (ball 0 C.radius) D.weight (-(D.weight i : ℝ)) 1 (C.coordinateField η i) := by
  let U : Opens (Fin (freeDimension a s p) → ℝ) := ⟨ball 0 C.radius,isOpen_ball⟩
  have h0 : (0 : Fin (freeDimension a s p) → ℝ) ∈ U := mem_ball_self C.radius_pos
  have hY : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (canonicalWordFrame D X j) Ω :=
    fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)
  apply fieldJetClass_one_of_radial_bracket_values U h0 D.weight (C.coordinateField η)
    (fun j => C.coordinateField_contDiffOn hY η hη j)
    (fun u hu => C.radial_identity Ω.isOpen hY η u hη hu)
    (fun j => C.basis_values Ω.isOpen hY η hη j)
  intro j l k hk
  have hkn : D.weight j + D.weight l < D.weight k := by exact_mod_cast hk
  have hjl : D.weight j + D.weight l ≤ s := by have hb := D.weight_bound k; omega
  rw [canonical_basis_bracket_expansion D Ω X hX C η hη j l hjl h0]
  simp only [C.basis_values Ω.isOpen hY η hη]
  have he : (∑ t, D.basis.equivFun (formalBasisCommutator D j l) t •
      (Pi.single t (1 : ℝ) : Fin (freeDimension a s p) → ℝ)) k =
      D.basis.equivFun (formalBasisCommutator D j l) k := by simp [Pi.single_apply]
  rw [he]
  exact formalBasisCommutator_coordinate_zero D j l k (by omega)
end RothschildStein.L1

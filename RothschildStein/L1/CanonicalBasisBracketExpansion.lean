-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FormalBasisCommutator
public import RothschildStein.L1.CanonicalRadialFrameIdentity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Canonical basis commutators within the cutoff have the exact
homogeneous constant expansion throughout the coefficient patch. -/
theorem canonical_basis_bracket_expansion {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (i j : Fin (freeDimension a s p)) (hij : D.weight i + D.weight j ≤ s)
    {u : Fin (freeDimension a s p) → ℝ} (hu : u ∈ ball 0 C.radius) :
    VectorField.lieBracket ℝ (C.coordinateField η i) (C.coordinateField η j) u =
      ∑ k, D.basis.equivFun (formalBasisCommutator D i j) k • C.coordinateField η k u := by
  have hq := C.coefficients (η,u) ⟨hη,hu⟩
  have hx := C.forward_mem (q := (η,u)) ⟨hη,hu⟩
  have hY (k : Fin (freeDimension a s p)) :=
    (G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D k)).contDiffAt
      (Ω.isOpen.mem_nhds hx)
  have he := C.pullbackField_lieBracket η (canonicalFrameMap C.time C.flow (η,u))
    hq.2.1 (canonicalWordFrame D X i) (canonicalWordFrame D X j) (hY i) (hY j)
  rw [hq.2.2] at he
  change VectorField.lieBracket ℝ (C.pullbackField η (canonicalWordFrame D X i))
    (C.pullbackField η (canonicalWordFrame D X j)) u = _
  rw [← he]
  change fderiv ℝ (fun ξ => C.theta (η,ξ)) (canonicalFrameMap C.time C.flow (η,u))
    (VectorField.lieBracket ℝ (wordBracket X (modelBasisWord D i))
      (wordBracket X (modelBasisWord D j)) (canonicalFrameMap C.time C.flow (η,u))) = _
  rw [actual_basis_bracket_eq_finiteLieField D Ω X hX i j hij hx]
  unfold finiteLieField
  rw [map_sum]
  simp only [map_smul]
  rfl
end RothschildStein.L1

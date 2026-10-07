-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FixedLiftData
public import RothschildStein.L1.TriangularBracketProjection

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1

/-- Horizontal projection carries actual lifted word
spanning to original word spanning, at the same weighted cutoff. -/
theorem stepSpansAt_triangularLift_projection {q n m s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin q → Fin m → MvPolynomial (Fin (n+m)) ℝ)
    {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ basePoint ⁻¹' Ω)
    (hspan : StepSpansAt w s (triangularLift X P) ξ) :
    StepSpansAt w s X (basePoint ξ) := by
  let S := {v | ∃ I : List (Fin q), I ≠ [] ∧ wordWeight w I ≤ s ∧
    v = wordBracket (triangularLift X P) I ξ}
  let T := {v | ∃ I : List (Fin q), I ≠ [] ∧ wordWeight w I ≤ s ∧
    v = wordBracket X I (basePoint ξ)}
  let L := (P1.paddingBaseCLM n m).toLinearMap
  have he : L '' S = T := by
    ext v
    constructor
    · rintro ⟨z,⟨I,hI,hW,rfl⟩,rfl⟩
      exact ⟨I,hI,hW,wordBracket_triangularLift_projection hΩ X hX P I ξ hξ⟩
    · rintro ⟨I,hI,hW,rfl⟩
      exact ⟨wordBracket (triangularLift X P) I ξ,⟨I,hI,hW,rfl⟩,
        wordBracket_triangularLift_projection hΩ X hX P I ξ hξ⟩
  have hsurj : Function.Surjective L := by
    intro y
    exact ⟨joinPoint y (0 : Fin m → ℝ),P1.paddingBaseCLM_join n m y 0⟩
  have hm : (Submodule.span ℝ S).map L = ⊤ := by
    rw [show Submodule.span ℝ S = ⊤ from hspan,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hsurj
  rw [Submodule.map_span,he] at hm
  exact hm

/-- A lifted open patch has an open projected base patch,
including zero-dimensional coordinate blocks. -/
theorem isOpen_basePoint_image {n m : ℕ} {U : Set (Fin (n+m) → ℝ)}
    (hU : IsOpen U) : IsOpen (basePoint '' U : Set (Fin n → ℝ)) := by
  have hm := isOpenMap_fst.comp (P1.paddingCoordinates n m).toHomeomorph.isOpenMap
  have he : IsOpenMap (basePoint (n := n) (m := m)) := by
    convert hm using 1
    funext ξ
    exact (P1.paddingBaseCLM_apply n m ξ).symm
  exact he U hU

/-- The base image of any free fixed-lift patch has the original
bracket condition everywhere, not merely at the selected center. -/
theorem FixedLiftData.original_bracketStepOn_image {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (L : FixedLiftData w s Ω X x₀ m)
    (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    bracketStepOn (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n+m) → ℝ))) w X s := by
  rintro x ⟨ξ,hξ,rfl⟩
  exact stepSpansAt_triangularLift_projection hΩ w X hX L.P
    (L.subset_domain hξ) (L.free_spanning ξ hξ).2

end RothschildStein.L1

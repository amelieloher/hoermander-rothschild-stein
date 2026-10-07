-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.BracketProjection
public import RothschildStein.L1.TriangularSmoothness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace

namespace RothschildStein.L1

/-- Every lifted word bracket has precisely the
original bracket as its horizontal projection throughout the ambient set. -/
theorem wordBracket_triangularLift_projection {q n m : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (I : List (Fin q)) : ∀ ξ ∈ basePoint ⁻¹' Ω,
      basePoint (wordBracket (triangularLift X P) I ξ) = wordBracket X I (basePoint ξ) := by
  have hbase : (⇑(P1.paddingBaseCLM n m) : (Fin (n + m) → ℝ) → (Fin n → ℝ)) =
      basePoint := funext (P1.paddingBaseCLM_apply n m)
  have hU : IsOpen (basePoint (n := n) (m := m) ⁻¹' Ω) := by
    simpa only [hbase] using hΩ.preimage (P1.paddingBaseCLM n m).continuous
  have hmap : MapsTo (P1.paddingBaseCLM n m) (basePoint ⁻¹' Ω) Ω := by
    intro ξ hξ
    simpa only [Set.mem_preimage, P1.paddingBaseCLM_apply] using hξ
  simpa only [hbase] using wordBracket_linear_projection hΩ hU (P1.paddingBaseCLM n m)
    hmap X (triangularLift X P) hX (fun i => contDiffOn_triangularLift X hX P i)
    (fun ξ _ i => by simpa only [P1.paddingBaseCLM_apply] using basePoint_triangularLift X P i ξ) I

end RothschildStein.L1

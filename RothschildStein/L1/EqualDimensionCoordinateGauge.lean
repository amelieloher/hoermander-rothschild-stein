-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ModelCoordinateGaugeConstruction
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.L1

/-- Equality transport retains the ambient gauge comparison for the same
coordinate data, on any equal-dimensional free carrier. -/
theorem exists_modelCoordinateData_with_ambient_gauge {N k s : ℕ}
    (w : Fin k → ℕ+) (hk : 0 < k) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (hN : N = freeDimension k s w) (V : Set (Fin N → ℝ)) (hV : IsOpen V)
    (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) V)
    (x : Fin N → ℝ) (hx : x ∈ V) (hstep : bracketStepOn V w X s)
    (hfree : ∀ y ∈ V, FreeAt w s X y) :
    ∃ M : ModelData k s N w, ∃ A : ModelCoordinateData V X x M,
      ∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ Ω : Set (Fin N → ℝ), V ⊆ Ω →
        ∀ η ∈ A.U, ∀ ξ ∈ A.U,
        ENNReal.ofReal (rsGauge M.G.weight M.G.weight_pos (A.Θ η ξ)/Cρ) ≤
          controlDistance Ω w X η ξ ∧
        controlDistance Ω w X η ξ ≤ ENNReal.ofReal
          (Cρ*rsGauge M.G.weight M.G.weight_pos (A.Θ η ξ)) := by
  cases k with
  | zero => omega
  | succ k =>
    subst N
    let D := G3.freeModelData w hk hw
    obtain ⟨A,Cρ,hCρ,hgauge⟩ := exists_modelCoordinateData_with_gauge D ⟨V,hV⟩
      X hX x hx hs hw hstep hfree
    exact ⟨modelDataOfFreeModel D,A,Cρ,hCρ,hgauge⟩
end RothschildStein.L1

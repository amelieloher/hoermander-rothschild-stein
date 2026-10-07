-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.EqualDimensionCoordinateGauge
public import RothschildStein.L1.FixedLiftCoordinateConstruction
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.L1

/-- The fixed lift constructs its coordinate data and
actual ambient gauge comparison together, on one common source. -/
theorem exists_fixedLift_coordinateApproximationData_with_gauge {n k s m : ℕ}
    {w : Fin k → ℕ+} {Ω : Set (Fin n → ℝ)}
    {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (L : FixedLiftData w s Ω X x₀ m) (hk : 0 < k) (hs : 1 ≤ s)
    (hw : ∀ i, (w i : ℕ) ≤ s) :
    ∃ M : ModelData k s (n+m) w, ∃ A : CoordinateApproximationData L M,
      ∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ η ∈ A.U, ∀ ξ ∈ A.U,
        ENNReal.ofReal (rsGauge M.G.weight M.G.weight_pos (A.Θ η ξ)/Cρ) ≤
          controlDistance {ξ : Fin (n+m) → ℝ | basePoint ξ ∈ Ω}
            w (triangularLift X L.P) η ξ ∧
        controlDistance {ξ : Fin (n+m) → ℝ | basePoint ξ ∈ Ω}
            w (triangularLift X L.P) η ξ ≤ ENNReal.ofReal
          (Cρ*rsGauge M.G.weight M.G.weight_pos (A.Θ η ξ)) := by
  have hstep : bracketStepOn (L.U : Set _) w (triangularLift X L.P) s := by
    intro ξ hξ
    exact (L.free_spanning ξ hξ).2
  obtain ⟨M,A,Cρ,hCρ,hgauge⟩ := exists_modelCoordinateData_with_ambient_gauge w hk hs hw
    L.dimension (L.U : Set _) L.U.isOpen (triangularLift X L.P)
    (fun i => (L.smooth i).mono L.subset_domain)
    (joinPoint x₀ (0 : Fin m → ℝ)) L.center_mem hstep
    (fun ξ hξ => (L.free_spanning ξ hξ).1)
  exact ⟨M,coordinateApproximationDataOfModel L M A,Cρ,hCρ,
    hgauge _ L.subset_domain⟩
end RothschildStein.L1

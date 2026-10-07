-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CoordinateApproximationData

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein.L1

/-- Ambient gauge comparison and uniform ball/fiber bounds
for one already fixed lift and coordinate patch (BB pp. 514–520).
The compact-center quantifier retains uniformity over compact center sets. This record makes no existence claim. -/
structure GaugeFiberData {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData k s (n+m) w} (A : CoordinateApproximationData L M) : Prop where
  gauge_comparison : ∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ η ∈ A.U, ∀ ξ ∈ A.U,
    ENNReal.ofReal (rsGauge M.G.weight M.G.weight_pos (A.Θ η ξ) / Cρ) ≤
      controlDistance {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η ξ ∧
    controlDistance {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η ξ ≤
      ENNReal.ofReal (Cρ * rsGauge M.G.weight M.G.weight_pos (A.Θ η ξ))
  ball_bounds : ∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ A.U →
    ∃ rstar cv Cv δ cf Cf : ℝ,
      0 < rstar ∧ 0 < cv ∧ 0 < Cv ∧ 0 < δ ∧ δ < 1 ∧ 0 < cf ∧ 0 < Cf ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
        let Ul := rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η r
        let Vb := rsBall Ω w X (basePoint η) r
        Ul ⊆ A.U ∧ MeasurableSet Ul ∧ MeasurableSet Vb ∧
        volume Ul ≠ ⊤ ∧ volume Vb ≠ ⊤ ∧
        0 < (volume Ul).toReal ∧ 0 < (volume Vb).toReal ∧
        cv * r ^ M.G.homogeneousDimension ≤ (volume Ul).toReal ∧
        (volume Ul).toReal ≤ Cv * r ^ M.G.homogeneousDimension ∧
        (∀ ξ ∈ Ul, controlDistance Ω w X (basePoint η) (basePoint ξ) ≤
          controlDistance {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η ξ) ∧
        (∀ z : Fin n → ℝ,
          fiberVolume Ul z ≤ ENNReal.ofReal (Cf * (volume Ul).toReal / (volume Vb).toReal)) ∧
        (∀ z ∈ rsBall Ω w X (basePoint η) (δ * r),
          ENNReal.ofReal (cf * (volume Ul).toReal / (volume Vb).toReal) ≤ fiberVolume Ul z)

end RothschildStein.L1

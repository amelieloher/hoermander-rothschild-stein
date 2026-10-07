-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.GaugeFiberData
public import RothschildStein.L1.CoordinateBallDensityFacts
public import RothschildStein.L1.FixedLiftCoordinateGauge
public import RothschildStein.L1.LiftedChartAssembly

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.L1

/-- The two fiber clauses of
`GaugeFiberData.ball_bounds`, verbatim and uniform on every compact center set of
the coordinate patch (BB (10.47)–(10.49), pp. 516–522). They involve the data
only through its patch `A.U`. -/
def CompactFiberBounds {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData k s (n+m) w} (A : CoordinateApproximationData L M) : Prop :=
  ∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ A.U →
    ∃ rstar δ cf Cf : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ 0 < cf ∧ 0 < Cf ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
        let Ul := rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η r
        let Vb := rsBall Ω w X (basePoint η) r
        (∀ z : Fin n → ℝ,
          fiberVolume Ul z ≤ ENNReal.ofReal (Cf * (volume Ul).toReal / (volume Vb).toReal)) ∧
        (∀ z ∈ rsBall Ω w X (basePoint η) (δ * r),
          ENNReal.ofReal (cf * (volume Ul).toReal / (volume Vb).toReal) ≤ fiberVolume Ul z)

namespace CoordinateApproximationData

/-- `GaugeFiberData` for coordinate data carrying the ambient gauge
comparison: the ball clauses come from the compact ball and density facts
of the fixed lift, the fiber clauses from `CompactFiberBounds`
(BB pp. 514–522). -/
theorem gaugeFiberData_of_fiberBounds {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData k s (n+m) w} (A : CoordinateApproximationData L M)
    (hΩ : IsOpen Ω) (hk : 0 < k) (hw : ∀ i, (w i : ℕ) ≤ s)
    (hgauge : ∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ η ∈ A.U, ∀ ξ ∈ A.U,
      ENNReal.ofReal (rsGauge M.G.weight M.G.weight_pos (A.Θ η ξ) / Cρ) ≤
        controlDistance {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η ξ ∧
      controlDistance {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η ξ ≤
        ENNReal.ofReal (Cρ * rsGauge M.G.weight M.G.weight_pos (A.Θ η ξ)))
    (hfib : CompactFiberBounds A) : GaugeFiberData A := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hs : 1 ≤ s := le_trans (w 0).pos (hw 0)
  refine ⟨hgauge, ?_⟩
  intro K hK hKU
  obtain ⟨r₁, cv, Cv, hr₁, hcv, hCv, hfacts⟩ := A.compact_ball_density_facts hΩ hs hw hK hKU
  obtain ⟨r₂, δ, cf, Cf, hr₂, hδ, hδ1, hcf, hCf, hfb⟩ := hfib K hK hKU
  refine ⟨min r₁ r₂, cv, Cv, δ, cf, Cf, lt_min hr₁ hr₂, hcv, hCv, hδ, hδ1, hcf, hCf, ?_⟩
  intro η hη r hr hrr
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ :=
    hfacts η hη r hr (lt_of_lt_of_le hrr (min_le_left _ _))
  obtain ⟨h₁₁, h₁₂⟩ := hfb η hη r hr (lt_of_lt_of_le hrr (min_le_right _ _))
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩

end CoordinateApproximationData

/-- The lifted chart, with the gauge-coordinated data of the
fixed lift; the only remaining input is the compact fiber clause, which involves
the coordinate data only through its patch (BB pp. 483–485, 514–522). -/
theorem exists_liftedChart_of_fiberBounds {n k : ℕ}
    (w : Fin k → ℕ+) (s : ℕ) (hk : 0 < k) (hw : ∀ i, (w i : ℕ) ≤ s)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ Ω) (hspan : StepSpansAt w s X x₀)
    (hFiber : ∀ (m : ℕ) (L : FixedLiftData w s Ω X x₀ m)
      (M : ModelData k s (n+m) w) (A : CoordinateApproximationData L M), CompactFiberBounds A) :
    ∃ m : ℕ, n+m = freeDimension k s w ∧ Nonempty (P1.LiftedChart w s Ω hΩ X x₀ m) := by
  have hs : 1 ≤ s := le_trans (w ⟨0, hk⟩).pos (hw ⟨0, hk⟩)
  obtain ⟨m, ⟨L⟩⟩ := exists_fixedLiftData w s Ω hΩ X hX x₀ hx₀ hspan
  obtain ⟨M, A, hgauge⟩ := exists_fixedLift_coordinateApproximationData_with_gauge L hk hs hw
  exact ⟨m, L.dimension, ⟨liftedChartOfData hΩ L M A
    (A.gaugeFiberData_of_fiberBounds hΩ hk hw hgauge (hFiber m L M A))⟩⟩

end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.GaugeFiberAssembly
public import RothschildStein.L1.JointShortChartFamily
public import RothschildStein.G4.AuxiliaryControl

/-!
# Fiber assembly interfaces

The compact fiber clause `CompactFiberBounds` is assembled from three ingredients:

* `CompactChartBuffers`:  finitely many paired original/lifted joint chart
  families whose `R/16` buffers cover a compact centre set;
* `StarredFiberBounds`:  single-scale fiber bounds for starred
  (auxiliary-distance) balls, normalised by the ordinary ball quotient;
* `CompactStarredComparison`:  compact-uniform inclusions between ordinary
  control balls and starred balls on the free patches.

The original patch is the projected free patch `basePoint '' L.U`, and the lifted
patch is `L.U`. These records assert properties of the given data.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.L1

variable {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData k s (n+m) w}

/-- Finitely
many paired joint chart families, original at threshold `1/2` on the projected
free patch and lifted at threshold `t` on the lifted free patch, whose `R/16`
buffers cover the compact centre set (BB pp. 448–449, 519–521). -/
def CompactChartBuffers (A : CoordinateApproximationData L M) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ A.U →
    ∃ N : ℕ, ∃ zo : Fin N → Fin n → ℝ, ∃ zl : Fin N → Fin (n + m) → ℝ,
    ∃ Fo : ∀ i, JointShortChartFamily (s := s) w
      (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) X (zo i) (1/2),
    ∃ Fl : ∀ i, JointShortChartFamily (s := s) w
      (L.U : Set (Fin (n + m) → ℝ)) (triangularLift X L.P) (zl i) t,
      ∀ η ∈ K, ∃ i, basePoint η ∈ closedBall (zo i) ((Fo i).R / 16) ∧
        η ∈ closedBall (zl i) ((Fl i).R / 16)

/-- Single-scale fiber bounds of
starred lifted balls over a starred original ball, normalised by the quotient of
the ordinary lifted and original ball volumes at the same radius. -/
def StarredFiberBounds (A : CoordinateApproximationData L M) : Prop :=
  ∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ A.U →
    ∃ r₀ cw cs cl cf Cf : ℝ, 0 < r₀ ∧ 0 < cw ∧ 0 < cs ∧ 0 < cl ∧ 0 < cf ∧ 0 < Cf ∧
      ∀ η ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ r₀ →
        let H := (volume (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w
            (triangularLift X L.P) η δ)).toReal /
          (volume (rsBall Ω w X (basePoint η) δ)).toReal
        ∀ y : Fin n → ℝ,
          G4.auxiliaryDistance (s := s) (basePoint (n := n) (m := m) '' (L.U : Set _)) w X
            (basePoint η) y < ENNReal.ofReal (cw * δ) →
          ENNReal.ofReal (cf * H) ≤ fiberVolume {ξ | G4.auxiliaryDistance (s := s)
            (L.U : Set (Fin (n + m) → ℝ)) w (triangularLift X L.P) η ξ <
              ENNReal.ofReal (cl * δ)} y ∧
          fiberVolume {ξ | G4.auxiliaryDistance (s := s)
            (L.U : Set (Fin (n + m) → ℝ)) w (triangularLift X L.P) η ξ <
              ENNReal.ofReal (cs * δ)} y ≤ ENNReal.ofReal (Cf * H)

/-- Compact-uniform comparison of
ordinary control balls (ambient domains) with starred balls (free patches) at
small radii: `d* ≤ d` and `d ≤ C d*`. -/
def CompactStarredComparison (A : CoordinateApproximationData L M) : Prop :=
  ∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ A.U →
    ∃ r₁ C : ℝ, 0 < r₁ ∧ 1 ≤ C ∧ ∀ η ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₁ →
      rsBall Ω w X (basePoint η) r ⊆
        {y | G4.auxiliaryDistance (s := s) (basePoint (n := n) (m := m) '' (L.U : Set _)) w X
          (basePoint η) y < ENNReal.ofReal (C * r)} ∧
      rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η r ⊆
        {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n + m) → ℝ)) w
          (triangularLift X L.P) η ξ < ENNReal.ofReal (C * r)} ∧
      {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n + m) → ℝ)) w
          (triangularLift X L.P) η ξ < ENNReal.ofReal r} ⊆
        rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η (C * r)

end RothschildStein.L1

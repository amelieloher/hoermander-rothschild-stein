-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderCylinderRepresentative
public import HeatKernel.Moser.HolderCylinderOscillation
public import HeatKernel.Geometry.CoordinateBall
public import HeatKernel.Moser.MeanValueWeakRestriction
import Mathlib.Tactic

/-! # Hölder representatives of bounded matrix weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein Filter Metric
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Coordinate product volume on parabolic Carnot space-time. -/
abbrev CarnotPoint.spaceTimeVolume {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq)) :
    Measure (ℝ × CarnotPoint G hq hqpos hspan) :=
  (MeasureTheory.volume : Measure ℝ).prod (CarnotPoint.volume G hq hqpos hspan)

/-- Carnot space-time volume is the original coordinate product volume. -/
theorem CarnotPoint.spaceTimeVolume_eq_coordinate {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq)) :
    (CarnotPoint.spaceTimeVolume G hq hqpos hspan : Measure (ℝ × (Fin N → ℝ))) =
      (MeasureTheory.volume : Measure (ℝ × (Fin N → ℝ))) := rfl

/-- Parabolic Carnot cylinders are the horizontal coordinate cylinders. -/
theorem parabolicCylinder_eq_horizontal {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : CarnotPoint G hq hqpos hspan) (t r : ℝ) :
    (@parabolicCylinder (CarnotPoint G hq hqpos hspan) _ x t r : Set (ℝ × (Fin N → ℝ))) =
      Ioo (t - r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x r := by
  change Ioo (t - r ^ 2) t ×ˢ (CarnotPoint.coordinateBall G hq hqpos hspan x r :
    Set (Fin N → ℝ)) = _
  rw [CarnotPoint.coordinateBall_eq_horizontalBall]

/-- Uniform cylinder contraction gives a continuous Hölder representative for a
bounded signed weak solution on a cylinder. -/
theorem exists_matrix_holder_representative_of_bounded_cylinder {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (c : ℕ → CarnotPoint G hq hqpos hspan) (hc : DenseRange c)
    (θ α : ℝ) (hθ : 0 ≤ θ) (hα : 0 < α)
    (hθα : θ ≤ (1 / 2 : ℝ) ^ α)
    (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (hcontraction : ∀ (x : Fin N → ℝ) (t r : ℝ), 0 < r →
      ∀ u : ℝ → (Fin N → ℝ) → ℝ,
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ u →
      IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ
        horizontalBall (G.horizontalFields hq) x (2 * r)))) (Function.uncurry u) →
      IsBoundedUnder (· ≥ ·)
      (ae (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ
        horizontalBall (G.horizontalFields hq) x (2 * r)))) (Function.uncurry u) →
    essSup (Function.uncurry u)
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x r)) -
      essInf (Function.uncurry u)
        (volume.restrict (Ioo (t - r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x r)) ≤
      θ *
        (essSup (Function.uncurry u)
            (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r))) -
          essInf (Function.uncurry u)
            (volume.restrict (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)))))
    (x₀ : CarnotPoint G hq hqpos hspan) (top r W : ℝ) (hr : 0 < r) (hW : 0 ≤ W)
    (u : ℝ → (Fin N → ℝ) → ℝ)
    (hu : IsLocalWeakSolution G hq hqpos hw hspan coeff
      ⟨Ioo (top - (2 * r) ^ 2) top, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) x₀ (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x₀ (2 * r)⟩ u)
    (hup : IsBoundedUnder (· ≤ ·)
      (ae ((CarnotPoint.spaceTimeVolume G hq hqpos hspan).restrict (parabolicCylinder x₀ top (2 * r))))
      (Function.uncurry u))
    (hlo : IsBoundedUnder (· ≥ ·)
      (ae ((CarnotPoint.spaceTimeVolume G hq hqpos hspan).restrict (parabolicCylinder x₀ top (2 * r))))
      (Function.uncurry u))
    (hglobal : essSup (Function.uncurry u)
        ((CarnotPoint.spaceTimeVolume G hq hqpos hspan).restrict (parabolicCylinder x₀ top (2 * r))) -
      essInf (Function.uncurry u)
        ((CarnotPoint.spaceTimeVolume G hq hqpos hspan).restrict (parabolicCylinder x₀ top (2 * r))) ≤ W) :
    ∃ v : ℝ × CarnotPoint G hq hqpos hspan → ℝ,
      ContinuousOn v (parabolicCylinder x₀ top r) ∧
      v =ᵐ[(CarnotPoint.spaceTimeVolume G hq hqpos hspan).restrict (parabolicCylinder x₀ top r)] Function.uncurry u ∧
      ∀ z ∈ parabolicCylinder x₀ top r, ∀ w ∈ parabolicCylinder x₀ top r,
        |v z - v w| ≤ (1024 / 15 : ℝ) ^ α *
          (dist ((parabolicSpaceTimeHomeomorph _).symm z)
            ((parabolicSpaceTimeHomeomorph _).symm w) / r) ^ α * W := by
  let μ := CarnotPoint.spaceTimeVolume G hq hqpos hspan
  let : μ.IsOpenPosMeasure := inferInstanceAs
    ((volume : Measure (ℝ × (Fin N → ℝ))).IsOpenPosMeasure)
  apply exists_continuous_representative_of_cylinder_contraction c hc μ
    (Function.uncurry u) x₀ top r α θ W hr hα
    hθ hθα hW hup hlo hglobal
  intro x t ρ hρ hsub
  have htime : Ioo (t - ρ ^ 2) t ⊆ Ioo (top - (2 * r) ^ 2) top := by
    intro s hs
    exact (hsub (a := (s, x)) ⟨hs, mem_ball_self hρ⟩).1
  have hspace : horizontalBall (G.horizontalFields hq) x ρ ⊆
      horizontalBall (G.horizontalFields hq) x₀ (2 * r) := by
    intro y hy
    have hy' : y ∈ ball x ρ := by
      change y ∈ (CarnotPoint.coordinateBall G hq hqpos hspan x ρ : Set (Fin N → ℝ))
      rwa [CarnotPoint.coordinateBall_eq_horizontalBall]
    have hs : t - ρ ^ 2 / 2 ∈ Ioo (t - ρ ^ 2) t := by
      constructor <;> nlinarith [sq_pos_of_pos hρ]
    have hb := (hsub (a := (t - ρ ^ 2 / 2, y)) ⟨hs, hy'⟩).2
    change y ∈ (CarnotPoint.coordinateBall G hq hqpos hspan x₀ (2 * r) : Set (Fin N → ℝ)) at hb
    rwa [CarnotPoint.coordinateBall_eq_horizontalBall] at hb
  have hweak : IsLocalWeakSolution G hq hqpos hw hspan coeff
      ⟨Ioo (t - 4 * (ρ / 2) ^ 2) t, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) x (2 * (ρ / 2)),
        isOpen_horizontalBall G hq hqpos hspan x (2 * (ρ / 2))⟩ u := by
    simpa only [show 4 * (ρ / 2) ^ 2 = ρ ^ 2 by ring, show 2 * (ρ / 2) = ρ by ring]
      using hu.mono htime hspace
  have hupper := hup.mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hlower := hlo.mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  rw [parabolicCylinder_eq_horizontal G hq hqpos hspan,
    CarnotPoint.spaceTimeVolume_eq_coordinate] at hupper hlower
  have hcontract := hcontraction x t (ρ / 2) (by positivity) u hweak
    (by simpa only [show 4 * (ρ / 2) ^ 2 = ρ ^ 2 by ring,
      show 2 * (ρ / 2) = ρ by ring] using hupper)
    (by simpa only [show 4 * (ρ / 2) ^ 2 = ρ ^ 2 by ring,
      show 2 * (ρ / 2) = ρ by ring] using hlower)
  simpa only [μ, parabolicCylinder_eq_horizontal G hq hqpos hspan,
    CarnotPoint.spaceTimeVolume_eq_coordinate,
    show 4 * (ρ / 2) ^ 2 = ρ ^ 2 by ring, show 2 * (ρ / 2) = ρ by ring] using hcontract

end HeatKernel

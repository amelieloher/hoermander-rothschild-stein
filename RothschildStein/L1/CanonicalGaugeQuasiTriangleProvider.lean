-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalAuxiliaryMetricComparison
public import RothschildStein.G1.WeightedTriangle
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.L1

/-- Actual canonical gauges satisfy the quasi-triangle inequality
on a common spatial patch. Original-domain extended distances avoid any
connectivity hypothesis outside that patch. -/
theorem exists_canonical_gauge_quasi_triangle {k s : ℕ} {p : Fin (k+1) → ℕ+}
    (D : G3.FreeModelData (k+1) s p) (hs : 0 < s)
    {Ω : Set (Fin (freeDimension (k+1) s p) → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin (freeDimension (k+1) s p) → ℝ) →
      (Fin (freeDimension (k+1) s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω p X s) (hFree : ∀ y ∈ Ω, FreeAt p s X y)
    {x : Fin (freeDimension (k+1) s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x) :
    ∃ r A : ℝ, 0 < r ∧ r ≤ C.radius ∧ 1 ≤ A ∧
      ∀ η ∈ ball x r, ∀ ξ ∈ ball x r, ∀ ζ ∈ ball x r,
      rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ)) ≤
        A * (rsGauge D.group.weight D.group.weight_pos (C.theta (η,ζ)) +
          rsGauge D.group.weight D.group.weight_pos (C.theta (ζ,ξ))) := by
  obtain ⟨r,A,hr,hrC,hA,he⟩ :=
    exists_canonical_auxiliary_metric_comparison D hs hΩ X hX hstep hFree C
  refine ⟨r,max 1 A,hr,hrC,le_max_left _ _,?_⟩
  intro η hη ξ hξ ζ hζ
  let ρ := fun y z => rsGauge D.group.weight D.group.weight_pos (C.theta (y,z))
  have hρ : ∀ y z, 0 ≤ ρ y z := fun y z => G2.gauge_nonneg D.group _
  have htri : G4.auxiliaryDistance (s := s) Ω p X η ξ ≤
      G4.auxiliaryDistance (s := s) Ω p X η ζ +
      G4.auxiliaryDistance (s := s) Ω p X ζ ξ :=
    G1.controlDistance_triangle Ω _ _ η ζ ξ
  have hh : ENNReal.ofReal (ρ η ξ) ≤ ENNReal.ofReal (A*(ρ η ζ + ρ ζ ξ)) := by
    calc
      ENNReal.ofReal (ρ η ξ) ≤ ENNReal.ofReal A * G4.auxiliaryDistance (s := s) Ω p X η ξ :=
        (he η hη ξ hξ).2
      _ ≤ ENNReal.ofReal A * (G4.auxiliaryDistance (s := s) Ω p X η ζ +
          G4.auxiliaryDistance (s := s) Ω p X ζ ξ) := by gcongr
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (ρ η ζ) + ENNReal.ofReal (ρ ζ ξ)) := by
        gcongr
        · exact (he η hη ζ hζ).1
        · exact (he ζ hζ ξ hξ).1
      _ = _ := by rw [← ENNReal.ofReal_add (hρ η ζ) (hρ ζ ξ),← ENNReal.ofReal_mul hA.le]
  have hrho : ρ η ξ ≤ A*(ρ η ζ + ρ ζ ξ) := by
    have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [ENNReal.toReal_ofReal (hρ η ξ),
      ENNReal.toReal_ofReal (mul_nonneg hA.le (add_nonneg (hρ η ζ) (hρ ζ ξ)))] using hh'
  exact hrho.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (add_nonneg (hρ η ζ) (hρ ζ ξ)))
end RothschildStein.L1

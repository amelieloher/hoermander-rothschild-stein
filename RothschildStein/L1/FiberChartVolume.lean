-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberChartImage
public import RothschildStein.Definitions.fiberVolume
public import RothschildStein.P1.PaddingCoordinates

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.L1

/-- The joined-coordinate fiber volume is exactly the
product-coordinate fiber measure, without a measure conversion factor. -/
theorem fiberVolume_joined_chart_image {n m : ℕ}
    (Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → ((Fin n → ℝ) × (Fin m → ℝ)))
    (S : Set ((Fin n → ℝ) × (Fin m → ℝ))) (y : Fin n → ℝ) :
    fiberVolume ((fun q => joinPoint (Φ q).1 (Φ q).2) '' S) y =
      volume {z : Fin m → ℝ | (y, z) ∈ Φ '' S} := by
  unfold fiberVolume
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, he⟩
    have hfirst := congrArg (P1.paddingBaseCLM n m) he
    have hsecond := congrArg (P1.paddingFiberCLM n m) he
    simp only [P1.paddingBaseCLM_join] at hfirst
    simp only [P1.paddingFiberCLM_join] at hsecond
    exact ⟨q, hq, Prod.ext hfirst hsecond⟩
  · rintro ⟨q, hq, he⟩
    refine ⟨q, hq, ?_⟩
    change joinPoint (Φ q).1 (Φ q).2 = joinPoint y z
    rw [he]

/-- The fiber of the actual joined chart image has the measure
of its vertical parameter image. This connects the Jacobian calculation
to the definition of `fiberVolume` (BB pp. 520–522). -/
theorem fiberVolume_parameterized_chart {n m : ℕ}
    {U : Set ((Fin n → ℝ) × (Fin m → ℝ))} {Q : Set (Fin m → ℝ)}
    (Φ : ((Fin n → ℝ) × (Fin m → ℝ)) → ((Fin n → ℝ) × (Fin m → ℝ)))
    (θ : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ)) (y : Fin n → ℝ)
    (hinj : ∀ v, InjOn (fun u => (Φ (u, v)).1) {u | (u, v) ∈ U})
    (hmap : ∀ v ∈ Q, (θ (y, v), v) ∈ U)
    (hbase : ∀ v ∈ Q, (Φ (θ (y, v), v)).1 = y) :
    fiberVolume ((fun q => joinPoint (Φ q).1 (Φ q).2) ''
      (U ∩ Prod.snd ⁻¹' Q)) y = volume ((fun v => (Φ (θ (y, v), v)).2) '' Q) := by
  rw [fiberVolume_joined_chart_image,
    fiber_chart_image_eq Φ θ y hinj hmap hbase]

end RothschildStein.L1

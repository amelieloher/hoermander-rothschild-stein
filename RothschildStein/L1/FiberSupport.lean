-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.TriangularProjection
public import RothschildStein.Definitions.fiberVolume

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.L1

/-- Lifted-ball fibers vanish outside the original ambient
ball. This uses the actual projection of measurable-control curves. -/
theorem fiberVolume_triangularLift_eq_zero_outside {a n m : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (ξ : Fin (n + m) → ℝ) (r : ℝ) (z : Fin n → ℝ)
    (hz : z ∉ rsBall Ω w X (basePoint ξ) r) :
    fiberVolume (rsBall (basePoint ⁻¹' Ω) w (triangularLift X P) ξ r) z = 0 := by
  have hs : {t : Fin m → ℝ | joinPoint z t ∈
      rsBall (basePoint ⁻¹' Ω) w (triangularLift X P) ξ r} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    apply hz
    apply rsBall_triangularLift_projection hΩ w X P ξ r
    refine ⟨joinPoint z t, ht, ?_⟩
    ext j
    simp [basePoint, joinPoint]
  unfold fiberVolume
  rw [hs, measure_empty]

end RothschildStein.L1

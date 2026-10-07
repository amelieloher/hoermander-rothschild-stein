-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Gauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Every continuous punctured homogeneous function is bounded
by its degree power of any homogeneous norm. Applied to Gamma and its
homogeneous derivatives, this is BB Theorem 6.20(1), printed p. 270. -/
theorem homogeneous_bound (ν : G2.HomogeneousNorm G) (a : ℝ)
    {f : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f ({(0 : Fin N → ℝ)}ᶜ))
    (hh : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x) :
    ∃ C > 0, ∀ x, x ≠ 0 → |f x| ≤ C * (ν x) ^ a := by
  have hk : IsCompact {x : Fin N → ℝ | ν x = 1} :=
    (G2.isCompact_gauge_le ν.gauge 1).of_isClosed_subset
      (isClosed_eq ν.gauge.1 continuous_const) (fun _ hx => hx.le)
  have hs : {x : Fin N → ℝ | ν x = 1} ⊆ {(0 : Fin N → ℝ)}ᶜ := by
    intro x hx he
    have hz := (ν.gauge.2.2.1 x).mpr he
    change ν x = 1 at hx
    linarith
  obtain ⟨B, hB⟩ := hk.exists_bound_of_continuousOn (hf.mono hs)
  refine ⟨max B 0 + 1, by positivity, fun x hx => ?_⟩
  have hp := G2.gauge_pos ν.gauge hx
  let z := G.dilate (ν x)⁻¹ x
  have hz : ν z = 1 := G2.gauge_normalize ν.gauge hx
  have hz0 : z ≠ 0 := hs hz
  have he : f x = (ν x) ^ a * f z := by
    have he := hh (ν x) hp z hz0
    rw [G2.dilate_normalize ν.gauge hx] at he
    exact he
  rw [he, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp a)]
  have hb : |f z| ≤ max B 0 + 1 := by
    have hb := hB z hz
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by linarith [le_max_left B 0])
  calc
    (ν x) ^ a * |f z| ≤ (ν x) ^ a * (max B 0 + 1) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hp a).le
    _ = (max B 0 + 1) * (ν x) ^ a := mul_comm _ _

end RothschildStein.H1

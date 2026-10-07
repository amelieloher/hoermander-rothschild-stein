-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.GaugeBalls
public import RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- The radius-r gauge sublevel is the dilation of the unit sublevel
(BB Thm 3.20, p. 105). -/
theorem gauge_sublevel_dilate {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {r : ℝ} (hr : 0 < r) :
    {x : Fin N → ℝ | ν x < r} = (G.dilate r) '' {x | ν x < 1} := by
  ext x
  constructor
  · intro hx
    change ν x < r at hx
    refine ⟨G.dilate r⁻¹ x, ?_, ?_⟩
    · change ν (G.dilate r⁻¹ x) < 1
      rw [hν.2.2.2 _ (inv_pos.mpr hr)]
      exact (inv_mul_lt_iff₀ hr).mpr (by simpa using hx)
    · ext j
      simp only [HomogeneousGroup.dilate, coordinateDilation]
      rw [inv_pow]
      field_simp
  · rintro ⟨y, hy, rfl⟩
    change ν (G.dilate r y) < r
    rw [hν.2.2.2 _ hr]
    change ν y < 1 at hy
    simpa using mul_lt_mul_of_pos_left hy hr

/-- Exact volume scaling of gauge balls under the exact
translation and dilation volume identities (BB Thm 3.20, p. 105). -/
theorem volume_gaugeBall_of_volumeScaling
    (htranslate : ∀ x : Fin N → ℝ, ∀ A : Set (Fin N → ℝ), volume ((G.mul x) '' A) = volume A)
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (gaugeBall G ν x r) =
      ENNReal.ofReal (r ^ G.homogeneousDimension) * volume {u : Fin N → ℝ | ν u < 1} := by
  rw [gaugeBall_image, htranslate, gauge_sublevel_dilate hν hr, hscale r hr]

/-- Exact doubling for balls of positive finite volume under translation and dilation scaling (BB Theorem 3.20, p. 105). -/
theorem volume_gaugeBall_doubling_of_volumeScaling
    (htranslate : ∀ x : Fin N → ℝ, ∀ A : Set (Fin N → ℝ), volume ((G.mul x) '' A) = volume A)
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (gaugeBall G ν x (2 * r)) =
      ENNReal.ofReal ((2 : ℝ) ^ G.homogeneousDimension) * volume (gaugeBall G ν x r) := by
  rw [volume_gaugeBall_of_volumeScaling htranslate hscale hν x (mul_pos (by norm_num) hr),
    volume_gaugeBall_of_volumeScaling htranslate hscale hν x hr, mul_pow,
    ENNReal.ofReal_mul (by positivity), mul_assoc]

end RothschildStein.G2

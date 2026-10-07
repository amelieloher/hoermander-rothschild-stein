-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.PowerIntegrals
public import RothschildStein.G2.BallTopology
public import RothschildStein.G2.GaugeConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Left translation preserves the volume of arbitrary sets
(BB Thm 3.6(d), p. 96; adapter to gauge-ball calculations). -/
theorem volume_leftTranslation_image {N : ℕ} (G : HomogeneousGroup N)
    (x : Fin N → ℝ) (A : Set (Fin N → ℝ)) : volume (G.mul x '' A) = volume A := by
  have h := (measurePreserving_leftTranslation G x).measure_preimage_emb
    (gaugeLeftTranslation G x).toMeasurableEquiv.measurableEmbedding (G.mul x '' A)
  have he : G.mul x ⁻¹' (G.mul x '' A) = A :=
    Set.preimage_image_eq _ (leftTranslation_bijective G x).injective
  rw [he] at h
  exact h.symm

/-- Unconditional consequence of the proved group measure identities
(BB pp. 104–106, Thm 3.20 / Prop 3.21). -/
theorem volume_gaugeBall
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (gaugeBall G ν x r) =
      ENNReal.ofReal (r ^ G.homogeneousDimension) * volume {u : Fin N → ℝ | ν u < 1} :=
  volume_gaugeBall_of_volumeScaling (volume_leftTranslation_image G) (fun _ ht A => volume_dilate_image G ht A) hν x hr

/-- Unconditional consequence of the proved group measure identities
(BB pp. 104–106, Thm 3.20 / Prop 3.21). -/
theorem volume_gaugeBall_doubling
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (gaugeBall G ν x (2 * r)) =
      ENNReal.ofReal ((2 : ℝ) ^ G.homogeneousDimension) * volume (gaugeBall G ν x r) :=
  volume_gaugeBall_doubling_of_volumeScaling (volume_leftTranslation_image G) (fun _ ht A => volume_dilate_image G ht A) hν x hr

/-- Unconditional consequence of the proved group measure identities
(BB pp. 104–106, Thm 3.20 / Prop 3.21). -/
theorem volume_gaugeSphere
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) :
    volume {y : Fin N → ℝ | gaugeDistance G ν y x = r} = 0 :=
  volume_gaugeSphere_of_volumeScaling (volume_leftTranslation_image G) (fun _ ht A => volume_dilate_image G ht A) hν x hr

/-- Unconditional consequence of the proved group measure identities
(BB pp. 104–106, Thm 3.20 / Prop 3.21). -/
theorem power_lintegral_near_finite_iff {N : ℕ} {G : HomogeneousGroup N}
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) (β : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫⁻ x in {x | ν x ≤ R}, ENNReal.ofReal ((ν x) ^ (-β))) ≠ ⊤ ↔ β < G.homogeneousDimension :=
  power_lintegral_near_finite_iff_of_volumeScaling (fun _ ht A => volume_dilate_image G ht A) hν β hR

/-- Unconditional consequence of the proved group measure identities
(BB pp. 104–106, Thm 3.20 / Prop 3.21). -/
theorem power_lintegral_near {N : ℕ} {G : HomogeneousGroup N}
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) {β R : ℝ}
    (hβ : β < G.homogeneousDimension) (hR : 0 < R) :
    (∫⁻ x in {x | ν x ≤ R}, ENNReal.ofReal ((ν x) ^ (-β))) =
      ENNReal.ofReal (G.homogeneousDimension : ℝ) * volume {x | ν x < 1} *
      ENNReal.ofReal (R ^ ((G.homogeneousDimension : ℝ) - β) / ((G.homogeneousDimension : ℝ) - β)) :=
  power_lintegral_near_of_volumeScaling (fun _ ht A => volume_dilate_image G ht A) hν hβ hR

end RothschildStein.G2

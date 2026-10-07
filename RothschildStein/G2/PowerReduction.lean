-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.RadialIntegration
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2

/-- Reduction of gauge powers on a radial Borel set to one-dimensional
powers, with the exact dilation-volume hypothesis (BB Prop 3.21, pp. 105–106). -/
theorem power_lintegral_restrict_of_volumeScaling {N : ℕ} {G : HomogeneousGroup N}
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (β : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫⁻ x in ν ⁻¹' s, ENNReal.ofReal ((ν x) ^ (-β))) =
      ENNReal.ofReal (G.homogeneousDimension : ℝ) * volume {x | ν x < 1} *
      ∫⁻ r in s ∩ Ioi (0 : ℝ), ENNReal.ofReal (r ^ ((G.homogeneousDimension : ℝ) - 1 - β)) := by
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-β))
  have hrad := radial_lintegral_of_volumeScaling hscale hν (s.indicator f)
    ((by fun_prop : Measurable f).indicator hs)
  have hleft : (fun x => s.indicator f (ν x)) = (ν ⁻¹' s).indicator (fun x => f (ν x)) := by
    ext x
    by_cases hx : ν x ∈ s <;> simp [hx]
  rw [hleft, lintegral_indicator (hν.1.measurable hs)] at hrad
  rw [hrad]
  congr 1
  have hind : (fun r : ℝ => ENNReal.ofReal (r ^ (G.homogeneousDimension - 1)) * s.indicator f r) =
      s.indicator (fun r => ENNReal.ofReal (r ^ (G.homogeneousDimension - 1)) * f r) := by
    ext r
    exact (indicator_mul_right s (fun r : ℝ => ENNReal.ofReal (r ^ (G.homogeneousDimension - 1))) f (i := r)).symm
  rw [hind, setLIntegral_indicator hs]
  apply setLIntegral_congr_fun (hs.inter measurableSet_Ioi)
  intro r hr
  dsimp only [f]
  rw [← ENNReal.ofReal_mul (pow_nonneg hr.2.le _), ← Real.rpow_natCast,
    ← Real.rpow_add hr.2]
  congr 2
  have hQ : 0 < G.homogeneousDimension := by
    unfold HomogeneousGroup.homogeneousDimension
    exact Finset.sum_pos (fun j _ => G.weight_pos j)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, G.dimension_pos⟩⟩)
  rw [Nat.cast_sub (by omega : 1 ≤ G.homogeneousDimension), Nat.cast_one]
  ring

/-- Closed gauge sublevels reduce to powers on `(0,R]`, including
all endpoint exponents (BB Prop 3.21, pp. 105–106; radial proof). -/
theorem power_lintegral_near_reduction_of_volumeScaling {N : ℕ} {G : HomogeneousGroup N}
    (hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Fin N → ℝ),
      volume ((G.dilate r) '' A) = ENNReal.ofReal (r ^ G.homogeneousDimension) * volume A)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) (β R : ℝ) :
    (∫⁻ x in {x | ν x ≤ R}, ENNReal.ofReal ((ν x) ^ (-β))) =
      ENNReal.ofReal (G.homogeneousDimension : ℝ) * volume {x | ν x < 1} *
      ∫⁻ r in Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ ((G.homogeneousDimension : ℝ) - 1 - β)) := by
  have h := power_lintegral_restrict_of_volumeScaling hscale hν β (s := Iic R) measurableSet_Iic
  have he : Iic R ∩ Ioi (0 : ℝ) = Ioc 0 R := by ext r; simp [and_comm]
  rw [he] at h
  exact h

end RothschildStein.G2

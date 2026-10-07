-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FieldCutoffCancellation
public import RothschildStein.H1.SharpShellCutoffSequence
public import RothschildStein.H1.SharpShellDominatedLimit
public import RothschildStein.H1.ShellRadialWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Actual standing field derivatives have vanishing
shell integrals at C¹ regularity, including the degree-two drift. -/
theorem StandingHypotheses.vanishingShellIntegrals_fieldDerivative
    (H : StandingHypotheses G q) (i : Fin (q + 1))
    {f ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hc : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hscale : ∀ s : ℝ, 0 < s → ∀ x, x ≠ 0 →
      f (G.dilate s x) = s ^ ((if i = 0 then 2 else 1) - (G.homogeneousDimension : ℝ)) * f x) :
    HasVanishingShellIntegrals ν (fieldDerivative (H.fields i) f) := by
  intro r R hr hrR
  obtain ⟨η, hη⟩ := exists_sharpShellCutoff_sequence G hν
  have hDf : ContinuousOn (fieldDerivative (H.fields i) f) {(0 : Fin N → ℝ)}ᶜ := by
    change ContinuousOn (fun x => fderiv ℝ f x (H.fields i x)) _
    exact (hc.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by norm_num)).clm_apply
      (H.fields_smooth G i).continuous.continuousOn
  have hz (n : ℕ) : ∫ x, fieldDerivative (H.fields i) f x *
      (η n (G.dilate R⁻¹ x) - η n (G.dilate r⁻¹ x)) = 0 := by
    have hn := gaugeCutoff_eventually_one G hν
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (sharpShell_innerRadius_ge_half n))
      (hη n).2.2.2.1
    exact H.integral_field_cutoffDifference_zero G i hc hscale (hη n).1
      (hη n).2.1 hn (inv_pos.mpr (hr.trans hrR)) (inv_pos.mpr hr)
  have ht := tendsto_integral_sharpShellCutoff_difference G hν hDf
    (fun n => (hη n).1.continuous) (fun n => (hη n).2.2.1)
    (fun n => (hη n).2.2.2.1) (fun n => (hη n).2.2.2.2) hr hrR
  have he : (fun n => ∫ x, fieldDerivative (H.fields i) f x *
      (η n (G.dilate R⁻¹ x) - η n (G.dilate r⁻¹ x))) = fun _ : ℕ => (0 : ℝ) := funext hz
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end RothschildStein.H1

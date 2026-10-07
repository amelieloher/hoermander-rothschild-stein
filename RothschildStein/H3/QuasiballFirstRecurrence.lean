-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballFirstScaleEstimate
public import RothschildStein.H3.LocalInterpolationStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The actual local fixed norms satisfy the quarter-contraction
recurrence with one constant independent of center, radius and input. -/
theorem quasiball_first_recurrence_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let γ := 2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (α : ℝ))
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin N → ℝ, ∀ R : ℝ, 0 < R → R ≤ Rmax →
      ∀ u f : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z R) 2 (α : ℝ) u →
      hasDistributionEquationWithDrift (quasiballDomain G ν z R) H.fields
        (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun (quasiballDomain G ν z R) u volume (⊤ : ℕ∞)) f →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → ∀ t s : ℝ, R / 2 ≤ t → t < s → s ≤ R →
      (holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z t) 1 (α : ℝ) u).toReal ≤
      (1 / 4) * (holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z s) 1 (α : ℝ) u).toReal +
      (c * η ^ (-γ) * lpNorm u ∞ (volume.restrict (G2.gaugeBall G ν z R))) / (s - t) ^ γ +
      η * lpNorm f ∞ (volume.restrict (G2.gaugeBall G ν z R)) := by
  let γ := 2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (α : ℝ))
  have hγ : 1 ≤ γ := by
    apply le_of_lt
    apply (one_lt_div (sub_pos.mpr hα1)).mpr
    linarith [show 0 ≤ (α : ℝ) from α.prop]
  obtain ⟨a, b, C, _ha, hb, hC, hscale⟩ := quasiball_first_scale_estimate_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hRmax
  let B := max (max (2 * a) Rmax) 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hBR : Rmax ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hBa : 2 * a ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB : 0 < B := by linarith
  let c := b * Rmax ^ (γ - 1) + C * B ^ γ
  have hc : 0 < c := add_pos (mul_pos hb (Real.rpow_pos_of_pos hRmax _))
    (mul_pos hC (Real.rpow_pos_of_pos hB _))
  refine ⟨c, hc, ?_⟩
  intro z R hR hRR u f hu heq η hη hη4 t s ht hts hs
  have hdR : s - t ≤ Rmax := by linarith
  exact local_interpolation_step_of_cutoff_bound ENNReal.toReal_nonneg lpNorm_nonneg lpNorm_nonneg
    hb.le hC.le (sub_pos.mpr hts) hdR hB1 hBR hBa hγ hη hη4
    (fun ε hε hε1 => hscale z R hR hRR u f hu heq t s ht hts hs ε hε hε1)

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballFirstRecurrence
public import RothschildStein.H3.LocalInterpolationStep
public import RothschildStein.H3.FrozenHolderRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Local first-order interpolation on smooth-gauge quasiballs, with the
stated loss and range of the small parameter, under the global control-norm
and metric-comparison hypotheses. -/
theorem quasiball_first_interpolation_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let γ := 2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (α : ℝ))
    ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ, ∀ R : ℝ, 0 < R → R ≤ Rmax →
      ∀ u f : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z R) 2 (α : ℝ) u →
      hasDistributionEquationWithDrift (quasiballDomain G ν z R) H.fields
        (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun (quasiballDomain G ν z R) u volume (⊤ : ℕ∞)) f →
      ∀ δ r : ℝ, 0 < δ → δ ≤ 1 / 2 → R / 2 ≤ r → r < R →
      (holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z r) 1 (α : ℝ) u).toReal ≤
      δ * lpNorm f ∞ (volume.restrict (G2.gaugeBall G ν z R)) +
      C * δ ^ (-γ) * (R - r) ^ (-γ) * lpNorm u ∞ (volume.restrict (G2.gaugeBall G ν z R)) := by
  let γ := 2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (α : ℝ))
  have hγ : 0 < γ := div_pos (by linarith) (sub_pos.mpr hα1)
  obtain ⟨c, hc, hrec⟩ := quasiball_first_recurrence_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hRmax
  let C := holeFillingConstant γ ^ (1 + γ) * c
  have hconst : 0 < holeFillingConstant γ := by linarith [holeFillingConstant_ge_two hγ]
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos hconst _) hc
  let Dgeom := S.groupControlGeometry_of_controlNorm G driftWeight H.fields Hc ⊤
  refine ⟨C, hC, ?_⟩
  intro z R hR hRR u f hu heq δ r hδ hδ2 hr hrR
  let ψ := fun t : ℝ => (holderXENorm driftWeight H.fields
    (controlDistance univ driftWeight H.fields) (quasiballDomain G ν z t) 1 (α : ℝ) u).toReal
  have hbounded : ∃ M : ℝ, ∀ t ∈ Icc (R / 2) R, ψ t ≤ M := by
    refine ⟨ψ R, ?_⟩
    intro t ht
    have hsub : (quasiballDomain G ν z t : Set (Fin N → ℝ)) ⊆ quasiballDomain G ν z R :=
      fun _ hx => hx.trans_le ht.2
    have hm := frozen_first_holderNorm_restrict_bound ⊤ (quasiballDomain G ν z R)
      (quasiballDomain G ν z t) Dgeom (subset_univ _) hsub H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) (show 0 < (α : ℝ) from hα) hu
    exact ENNReal.toReal_mono hm.2.ne hm.1
  exact local_interpolation_of_scalar_recurrence (half_pos hR).le (by linarith)
    hγ hc.le lpNorm_nonneg lpNorm_nonneg (fun _ _ => ENNReal.toReal_nonneg) hbounded
    (fun η hη hη4 t s ht hts hs => hrec z R hR hRR u f hu heq η hη hη4 t s ht hts hs)
    hδ hδ2 hr hrR le_rfl

end RothschildStein.H3

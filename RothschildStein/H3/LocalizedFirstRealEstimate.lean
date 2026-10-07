-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalizedFirstEquationEstimate
public import RothschildStein.H3.FrozenHolderEquationNormData
public import RothschildStein.H3.HolderCutoffToReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- Actual finite local input and forcing norms convert the
fixed equation coefficient estimate to the real scale inequality used
by radius iteration. All finiteness is derived from the fixed input. -/
theorem localized_first_equation_real_estimate_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ,
      ∀ U V : Opens (Fin N → ℝ),
      (U : Set (Fin N → ℝ)) ⊆ G2.gaugeBall G Hc.norm z ρ →
      ∀ u : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        U 2 (α : ℝ) u →
      ∀ f : (Fin N → ℝ) → ℝ,
      hasDistributionEquationWithDrift U H.fields
        (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun U u volume (⊤ : ℕ∞)) f →
      ∀ φ : TestFunction U ℝ (⊤ : ℕ∞), EqOn φ 1 (V : Set (Fin N → ℝ)) →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      eLpNorm φ ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ≤ 1 →
      (∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤
        (volume.restrict (U : Set (Fin N → ℝ))) ≤ ENNReal.ofReal A) →
      eLpNorm (sumSquaresWithDrift H.fields φ) ⊤
        (volume.restrict (U : Set (Fin N → ℝ))) ≤ ENNReal.ofReal B →
      ∀ η : ℝ, 0 < η → η < 1 →
      (holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        V 1 (α : ℝ) u).toReal ≤
        η * (lpNorm f ∞ (volume.restrict (U : Set (Fin N → ℝ))) +
          B * lpNorm u ∞ (volume.restrict (U : Set (Fin N → ℝ))) +
          2 * A * (holderXENorm driftWeight H.fields
            (controlDistance univ driftWeight H.fields) U 1 (α : ℝ) u).toReal) +
        C * η ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (α : ℝ)))) *
          lpNorm u ∞ (volume.restrict (U : Set (Fin N → ℝ))) := by
  obtain ⟨C, hC, hb⟩ := localized_first_equation_coefficient_estimate_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hρ
  let Dgeom := S.groupControlGeometry_of_controlNorm G driftWeight H.fields Hc ⊤
  refine ⟨C, hC, ?_⟩
  intro z U V hU u hu f heq φ hφ A B hA0 hB0 hn hA hB η hη hη1
  obtain ⟨huTop, hfTop, hfirst⟩ := frozen_holder_equation_norm_data ⊤ U Dgeom
    (subset_univ _) H.fields (fun i => (H.fields_smooth G i).contDiffOn)
    (show 0 < (α : ℝ) from hα) u f hu heq
  have hh := hb z U V hU u hu f heq φ hφ (ENNReal.ofReal A) (ENNReal.ofReal B)
    hn hA hB η hη hη1
  exact holder_cutoff_coefficients_toReal hfTop.eLpNorm_ne_top huTop.eLpNorm_ne_top
    hfirst.ne hη hA0 hB0 hC.le hh

end RothschildStein.H3

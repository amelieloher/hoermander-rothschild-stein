-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalRepresentativeGeometry
public import RothschildStein.H3.WeakOperatorDistributionEquation
public import RothschildStein.Provider.GroupRegularityInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Local regularity for distributions solving the stated equation, for
every finite p > 1 and without flow or density hypotheses
(BB pp. 374–375). -/
theorem localLpRegularity_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields) :
    ∀ p : ℝ≥0∞, 1 < p → p < ⊤ →
      ∀ Ω : Opens (Fin N → ℝ),
      ∀ T : Distribution Ω ℝ (⊤ : ℕ∞), ∀ f : (Fin N → ℝ) → ℝ,
        memSobolevXLoc driftWeight H.fields Ω 0 p f →
        hasDistributionEquationWithDrift Ω H.fields
          (fun i => (H.fields_smooth G i).contDiffOn) T f →
        ∃ u : (Fin N → ℝ) → ℝ, representsDistribution Ω T u ∧
          memSobolevXLoc driftWeight H.fields Ω 2 p u := by
  intro p hp hpt Ω T f hf heq
  have hpt' : p ≠ ⊤ := hpt.ne
  have hpReal : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt').2 hp
  let hpFact : Fact (1 ≤ p) := ⟨hp.le⟩
  let hpRealFact : Fact (1 ≤ ENNReal.ofReal p.toReal) := ⟨by
    simpa only [ENNReal.ofReal_toReal hpt'] using hp.le⟩
  let r : ℝ≥0∞ := (1-p⁻¹)⁻¹
  let hpr : ENNReal.HolderConjugate p r := ⟨by
    change p⁻¹ + ((1-p⁻¹)⁻¹)⁻¹ = (1 : ℝ≥0∞)⁻¹
    rw [inv_inv, inv_one]
    apply add_tsub_cancel_of_le
    simpa only [inv_one] using (ENNReal.inv_le_inv.mpr hp.le)⟩
  let hprReal : ENNReal.HolderConjugate (ENNReal.ofReal p.toReal) r := by
    simpa only [ENNReal.ofReal_toReal hpt'] using hpr
  let hrFact : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r p⟩
  have hf' : ∀ V : Opens (Fin N → ℝ), IsCompact (closure (V : Set (Fin N → ℝ))) →
      closure (V : Set (Fin N → ℝ)) ⊆ Ω →
      MemLp f (ENNReal.ofReal p.toReal) (volume.restrict (V : Set (Fin N → ℝ))) := by
    intro V hV hVΩ
    simpa only [ENNReal.ofReal_toReal hpt'] using (hf V hV hVΩ).1
  obtain ⟨u,hu,hrep⟩ := local_sobolev_representative_of_controlNorm G H K hQ P
    p.toReal hpReal r Ω T f hf' heq
  exact ⟨u,hrep,by simpa only [ENNReal.ofReal_toReal hpt'] using hu⟩

end RothschildStein.H3

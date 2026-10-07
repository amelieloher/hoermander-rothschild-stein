-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PrescribedGaugeHalfRadius
public import RothschildStein.H3.DriftFirstWordSum
public import RothschildStein.H3.SobolevSecondNormBound
public import RothschildStein.H3.QuasiballDomainRestriction
public import RothschildStein.H3.WeakOperatorDistributionEquation
public import RothschildStein.H3.FrozenDriftEquationBridge
public import RothschildStein.Provider.GroupRegularityInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal
namespace RothschildStein.H3

/-- The prescribed-gauge Lp estimate is uniform in the center and radius
(BB pp. 374–375). -/
theorem quasiballLpTransfer_holds {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (_hsym : ∀ x, ν (G.inv x) = ν x) :
    Provider.QuasiballLpTransfer G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) ν := by
  dsimp only [Provider.QuasiballLpTransfer]
  intro p hp hpt
  let hpFact : Fact (1 ≤ p) := ⟨hp.le⟩
  obtain ⟨A, hA, hest⟩ := halfRadius_estimate_prescribed_gauge G H K hQ ν hν p hp hpt
  refine ⟨A, hA, ?_⟩
  intro z r hr U V hU hV u hu
  have domains : ∀ (W : Opens (Fin N → ℝ)) (s : ℝ),
      (∀ x, x ∈ W ↔ ν (G.mul (G.inv z) x) < s) → W = quasiballDomain G ν z s := by
    intro W s hW
    ext x
    exact hW x
  have heU := domains U r hU
  have heV := domains V (r / 2) hV
  subst U
  subst V
  obtain ⟨D⟩ := exists_weakDriftOperatorData H.fields (quasiballDomain G ν z r) p u hu
  refine ⟨D.operator, D.operator_memLp, ⟨?_, ?_⟩, ?_⟩
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      (D.operator_memLp.locallyIntegrable hp.le)
  · intro ψ
    have heq := D.ofFun_adjoint_equation hp.le
      (fun i => (H.fields_smooth G i).contDiffOn) D.operator ae_eq_rfl ψ
    rw [adjointTest_zero_eq_driftTransposeTest] at heq
    exact heq
  · rw [sum_driftFirstWordFamily]
    change driftSecondWeakENorm H.fields (quasiballDomain G ν z (r / 2)) p u +
      ENNReal.ofReal r⁻¹ * horizontalWeakENorm H.fields (quasiballDomain G ν z (r / 2)) p u +
      ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict ((quasiballDomain G ν z (r / 2)) : Set (Fin N → ℝ))) ≤ _
    have hv := memSobolevX_quasiball_restrict G ν z (show r/2 ≤ r by linarith)
      driftWeight H.fields 2 p u hu
    have hs := (driftSecondWeakENorm_lt_top H.fields _ p u hv).ne
    have hh := (horizontalWeakENorm_lt_top H.fields _ p u hv).ne
    have hf := D.operator_memLp.eLpNorm_ne_top
    have hu0 := hu.1.eLpNorm_ne_top
    have hv0 := hv.1.eLpNorm_ne_top
    have hi : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
    have hn : driftSecondWeakENorm H.fields (quasiballDomain G ν z (r / 2)) p u +
        ENNReal.ofReal r⁻¹ * horizontalWeakENorm H.fields (quasiballDomain G ν z (r / 2)) p u +
        ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict ((quasiballDomain G ν z (r / 2)) : Set (Fin N → ℝ))) ≠ ⊤ := by
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
        ⟨hs, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh⟩,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv0⟩
    rw [← ENNReal.ofReal_toReal hn]
    apply (ENNReal.ofReal_le_ofReal ?_).trans_eq
      (show ENNReal.ofReal (A*((eLpNorm D.operator p (volume.restrict ((quasiballDomain G ν z r) : Set (Fin N → ℝ)))).toReal +
        r⁻¹^2*(eLpNorm u p (volume.restrict ((quasiballDomain G ν z r) : Set (Fin N → ℝ)))).toReal)) = _ from by
        rw [ENNReal.ofReal_mul hA.le, ENNReal.ofReal_add ENNReal.toReal_nonneg
          (mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg), ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_toReal hf, ENNReal.ofReal_toReal hu0])
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hs,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh⟩)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv0),
      ENNReal.toReal_add hs (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hi, ENNReal.toReal_ofReal (sq_nonneg _)]
    exact hest z r hr u hu D

end RothschildStein.H3

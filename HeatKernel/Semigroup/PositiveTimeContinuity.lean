-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.PositiveTimeHeatOperators
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Operator-norm continuity away from time zero

On a compact positive time interval, the heat and generator multipliers are jointly
continuous with the spectral variable. Compactness gives uniform convergence of sections,
which passes through continuous functional calculus.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel

theorem continuousOn_heatMultiplier_rectangle {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => heatMultiplier p.1 p.2) (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  have hn : ∀ p ∈ Icc a b ×ˢ Icc (0 : ℝ) 1, p.1 ≠ 0 :=
    fun p hp => (lt_of_lt_of_le ha hp.1.1).ne'
  exact continuous_fst.rexp.continuousOn.mul
    ((expNegInvGlue.contDiff (n := 0)).continuous.comp_continuousOn
      (continuous_snd.continuousOn.div continuous_fst.continuousOn hn))

theorem continuousOn_heatResolventFactor_rectangle {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => heatResolventFactor p.1 p.2) (Icc a b ×ˢ Icc (0 : ℝ) 1) := by
  have hn : ∀ p ∈ Icc a b ×ˢ Icc (0 : ℝ) 1, p.1 ≠ 0 :=
    fun p hp => (lt_of_lt_of_le ha hp.1.1).ne'
  simp_rw [heatResolventFactor_eq]
  exact (continuous_fst.rexp.continuousOn.div continuous_fst.continuousOn hn).mul
    ((expNegInvGlue.continuous_polynomial_eval_inv_mul Polynomial.X).comp_continuousOn
      (continuous_snd.continuousOn.div continuous_fst.continuousOn hn))

theorem continuousOn_heatGeneratorMultiplier_rectangle {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => heatGeneratorMultiplier p.1 p.2) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
  (continuous_const.sub continuous_snd).continuousOn.mul (continuousOn_heatResolventFactor_rectangle ha)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem continuousAt_cfc_of_continuousOn_rectangle (R : E →L[ℂ] E)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (F : ℝ → ℝ → ℝ)
    {a b t : ℝ} (hat : a < t) (htb : t < b)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hsections : ∀ s, ContinuousOn (F s) (Icc (0 : ℝ) 1)) :
    ContinuousAt (fun s => (cfc (F s) R : E →L[ℂ] E)) t := by
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF
  have hl := hu.tendstoUniformlyOn (show t ∈ Icc a b from ⟨hat.le, htb.le⟩)
  rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hat htb)] at hl
  exact continuousAt_cfc_fun (hl.mono hspec)
    (Eventually.of_forall (fun s => (hsections s).mono hspec))

theorem continuousAt_positiveTimeHeatOperator (R : E →L[ℂ] E)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (positiveTimeHeatOperator R) t :=
  continuousAt_cfc_of_continuousOn_rectangle R hspec heatMultiplier
    (show t / 2 < t by linarith) (show t < 2 * t by linarith)
    (continuousOn_heatMultiplier_rectangle (show 0 < t / 2 by positivity))
    (fun s => (continuous_heatMultiplier s).continuousOn)

theorem continuousAt_heatGeneratorOperator (R : E →L[ℂ] E)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (heatGeneratorOperator R) t :=
  continuousAt_cfc_of_continuousOn_rectangle R hspec heatGeneratorMultiplier
    (show t / 2 < t by linarith) (show t < 2 * t by linarith)
    (continuousOn_heatGeneratorMultiplier_rectangle (show 0 < t / 2 by positivity))
    (fun s => (continuous_heatGeneratorMultiplier s).continuousOn)

end HeatKernel

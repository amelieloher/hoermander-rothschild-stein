-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualIntegralIdentity
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Weak time balances in a continuous form dual -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- The dual-valued weak time equation, including Bochner integrability and
 every scalar evaluation against a fixed form test. -/
def SatisfiesDualTimeBalance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Set ℝ) (D F : ℝ → (E →L[ℝ] ℝ)) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ J →
    Integrable (fun t => deriv ψ t • D t) (volume.restrict J) ∧
    Integrable (fun t => ψ t • F t) (volume.restrict J) ∧
    (∫ t in J, deriv ψ t • D t) = (∫ t in J, ψ t • F t) ∧
    ∀ v : E,
      Integrable (fun t => deriv ψ t * D t v) (volume.restrict J) ∧
      Integrable (fun t => ψ t * F t v) (volume.restrict J) ∧
      (∫ t in J, deriv ψ t * D t v) = ∫ t in J, ψ t * F t v

/-- Scalar weak balances of dual-valued L² curves give the full Bochner weak
 time balance on every compact time set. -/
theorem satisfiesDualTimeBalance_of_memLp_of_eval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {J : Set ℝ} (hJ : IsCompact J)
    {D F : ℝ → (E →L[ℝ] ℝ)}
    (hD : MemLp D 2 (volume.restrict J)) (hF : MemLp F 2 (volume.restrict J))
    (hscalar : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ J →
      ∀ v : E,
        Integrable (fun t => deriv ψ t * D t v) (volume.restrict J) ∧
        Integrable (fun t => ψ t * F t v) (volume.restrict J) ∧
        (∫ t in J, deriv ψ t * D t v) = ∫ t in J, ψ t * F t v) :
    SatisfiesDualTimeBalance J D F := by
  intro ψ hψ hcψ hsψ
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJ.measure_lt_top.ne
  have hiD := integrable_bounded_smul_dual_of_memLp_two
    ((hψ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hcψ.deriv (volume.restrict J)) hD
  have hiF := integrable_bounded_smul_dual_of_memLp_two
    (hψ.continuous.memLp_top_of_hasCompactSupport hcψ (volume.restrict J)) hF
  exact ⟨hiD, hiF, integral_smul_dual_eq_of_eval hiD hiF
    (fun v => (hscalar ψ hψ hcψ hsψ v).2.2), hscalar ψ hψ hcψ hsψ⟩

/-- The weak dual time balance is unchanged by almost-everywhere changes of
 the chosen value and flux representatives. -/
theorem SatisfiesDualTimeBalance.congr {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {J : Set ℝ}
    {D F D' F' : ℝ → (E →L[ℝ] ℝ)} (h : SatisfiesDualTimeBalance J D F)
    (hD : D =ᵐ[volume.restrict J] D') (hF : F =ᵐ[volume.restrict J] F') :
    SatisfiesDualTimeBalance J D' F' := by
  intro ψ hψ hcψ hsψ
  obtain ⟨hiD, hiF, heq, hv⟩ := h ψ hψ hcψ hsψ
  have hd : (fun t => deriv ψ t • D t) =ᵐ[volume.restrict J]
      (fun t => deriv ψ t • D' t) := hD.mono fun t ht => congrArg (fun x => deriv ψ t • x) ht
  have hf : (fun t => ψ t • F t) =ᵐ[volume.restrict J]
      (fun t => ψ t • F' t) := hF.mono fun t ht => congrArg (fun x => ψ t • x) ht
  refine ⟨hiD.congr hd, hiF.congr hf,
    (integral_congr_ae hd).symm.trans (heq.trans (integral_congr_ae hf)), ?_⟩
  intro v
  obtain ⟨hvd, hvf, hve⟩ := hv v
  have hds : (fun t => deriv ψ t * D t v) =ᵐ[volume.restrict J]
      (fun t => deriv ψ t * D' t v) := hD.mono fun t ht => congrArg (fun x => deriv ψ t * x v) ht
  have hfs : (fun t => ψ t * F t v) =ᵐ[volume.restrict J]
      (fun t => ψ t * F' t v) := hF.mono fun t ht => congrArg (fun x => ψ t * x v) ht
  exact ⟨hvd.congr hds, hvf.congr hfs,
    (integral_congr_ae hds).symm.trans (hve.trans (integral_congr_ae hfs))⟩

end HeatKernel

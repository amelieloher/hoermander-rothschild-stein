-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.TimeIntegratedFormTests
import Mathlib.Tactic

/-! # Combined integral identities extended by horizontal form density -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- An identity for the combined integrand extends to zero-boundary form tests.
The L² representatives justify separating the integrals on the smooth core. -/
theorem timeIntegratedFormTest_eq_zero_of_combined_identity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (T : Lp ℝ 2 (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
    (F : Fin q → Lp ℝ 2 (μ.prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
    (hweak : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (V : Set (Fin N → ℝ)) →
      (∫ z : α × (Fin N → ℝ), T z * φ z.2 +
        ∑ i, F i z * fieldDerivative (X i) φ z.2 ∂μ.prod volume) = 0)
    (v : zeroBoundaryGraph V X) :
    timeIntegratedFormTest μ X T F ⟨v, zeroBoundaryGraph_le_energyGraph V X v.property⟩ = 0 := by
  apply timeIntegratedFormTest_eq_zero_of_core μ X V T F _ v
  intro w hw
  obtain ⟨φ, hφ, hc, hs, hv, hg⟩ := hw
  have hT' : MemLp (T : α × (Fin N → ℝ) → ℝ) 2 (μ.prod volume) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp T
  have hF' (i : Fin q) : MemLp (F i : α × (Fin N → ℝ) → ℝ) 2 (μ.prod volume) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (F i)
  have hv' : MemLp φ 2 (volume : Measure (Fin N → ℝ)) := by
    apply (memLp_congr_ae hv).mp
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (w : GradientSpace (N := N) ⊤ q).fst
  have hg' (i : Fin q) : MemLp (fieldDerivative (X i) φ) 2
      (volume : Measure (Fin N → ℝ)) := by
    apply (memLp_congr_ae (hg i)).mp
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((w : GradientSpace (N := N) ⊤ q).snd i)
  have hi : Integrable (fun z : α × (Fin N → ℝ) => T z * φ z.2) (μ.prod volume) :=
    hT'.integrable_mul (hv'.comp_snd μ)
  have hj (i : Fin q) : Integrable (fun z : α × (Fin N → ℝ) =>
      F i z * fieldDerivative (X i) φ z.2) (μ.prod volume) :=
    (hF' i).integrable_mul ((hg' i).comp_snd μ)
  have he := hweak φ hφ hc hs
  rw [integral_add hi (integrable_finsetSum Finset.univ (fun i _ => hj i)),
    integral_finsetSum Finset.univ (fun i _ => hj i)] at he
  rw [timeIntegratedFormTest_apply]
  apply Eq.trans _ he
  apply congrArg₂ (· + ·)
  · apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_snd (μ := μ) (ν := volume) |>.ae_eq_comp hv]
      with z hz
    exact congrArg (fun r => T z * r) hz
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_snd (μ := μ) (ν := volume) |>.ae_eq_comp (hg i)]
      with z hz
    exact congrArg (fun r => F i z * r) hz

end HeatKernel

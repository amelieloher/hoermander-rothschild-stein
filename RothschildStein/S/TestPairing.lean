-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.DistributionWords
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal Distributions
namespace RothschildStein.S
variable {n : ℕ}

/-- Integration against a compact smooth test is a continuous linear
functional on Lᵖ, including p = 1 (BB pp. 68–69). -/
def lpTestPairingCLM (Ω : Opens (Fin n → ℝ)) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ))) →L[ℝ] ℝ :=
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  let hψ : MemLp ψ r μ := ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p r).flip (hψ.toLp ψ)

/-- Evaluation of the Lᵖ test functional (BB p. 68). -/
theorem lpTestPairingCLM_apply (Ω : Opens (Fin n → ℝ)) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (f : Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ)))) :
    lpTestPairingCLM Ω p r ψ f = ∫ x in (Ω : Set (Fin n → ℝ)), f x * ψ x := by
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  let hψ : MemLp ψ r μ := ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  change (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p r f (hψ.toLp ψ) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hψ.coeFn_toLp] with x hx
  change f x * hψ.toLp ψ x = f x * ψ x
  rw [hx]

/-- Lᵖ convergence implies convergence of every test integral
(BB pp. 68–69). -/
theorem tendsto_testIntegral_of_tendsto_eLpNorm {α : Type*} {l : Filter α}
    (Ω : Opens (Fin n → ℝ)) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (F : α → (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hF : ∀ j, MemLp (F j) p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hf : MemLp f p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (ht : Tendsto (fun j => eLpNorm (fun x => F j x - f x) p
      (volume.restrict (Ω : Set (Fin n → ℝ)))) l (𝓝 0)) :
    Tendsto (fun j => ∫ x in (Ω : Set (Fin n → ℝ)), F j x * ψ x) l
      (𝓝 (∫ x in (Ω : Set (Fin n → ℝ)), f x * ψ x)) := by
  have hLp : Tendsto (fun j => (hF j).toLp (F j)) l (𝓝 (hf.toLp f)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f hf).mpr
    exact ht
  have hc := (lpTestPairingCLM Ω p r ψ).continuous.tendsto (hf.toLp f) |>.comp hLp
  have he : ∀ (g : (Fin n → ℝ) → ℝ)
      (hg : MemLp g p (volume.restrict (Ω : Set (Fin n → ℝ)))),
      lpTestPairingCLM Ω p r ψ (hg.toLp g) =
        ∫ x in (Ω : Set (Fin n → ℝ)), g x * ψ x := by
    intro g hg
    rw [lpTestPairingCLM_apply]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  rw [he f hf] at hc
  exact hc.congr (fun j => he (F j) (hF j))

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalWeakScalarChainRule
public import HeatKernel.Sobolev.LowerTruncatedLogarithm
import Mathlib.Tactic

/-! # Literal weak gradients of positive local energy logarithms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A positive lower bound gives local energy membership of the literal logarithm
and the reciprocal chain rule for the supplied original weak gradient. -/
theorem MemLocalEnergy.log_with_weak_gradient_of_ae_lower_bound {N q : ℕ}
    {U : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {f : (Fin N → ℝ) → ℝ} (hf : MemLocalEnergy U X f)
    {g : Fin q → (Fin N → ℝ) → ℝ} (hg : ∀ i, hasWeakWordDeriv X U [i] f (g i))
    {c : ℝ} (hc : 0 < c) (hlower : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), c ≤ f x) :
    MemLocalEnergy U X (Real.log ∘ f) ∧
      ∀ i, hasWeakWordDeriv X U [i] (Real.log ∘ f) (fun x => g i x / f x) := by
  obtain ⟨hlog, hgrad⟩ := hf.comp_piecewise_with_weak_gradient hX hg
    (Sobolev.lipschitzWith_lowerTruncatedLog hc) ({c} : Set ℝ) (countable_singleton c)
    (fun s hs => Sobolev.contDiffAt_lowerTruncatedLog hc (by simpa only [mem_singleton_iff] using hs))
    (fun s hs => Sobolev.lowerTruncatedLogSlope_eq_deriv hc (by simpa only [mem_singleton_iff] using hs))
  have heq : Sobolev.lowerTruncatedLog c ∘ f =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      Real.log ∘ f := by
    filter_upwards [hlower] with x hx
    simp only [Function.comp_apply, Sobolev.lowerTruncatedLog, max_eq_right hx]
  refine ⟨hlog.congr_ae U X heq, fun i => ?_⟩
  apply RothschildStein.S.hasWeakWordDeriv_congr_ae X U (hgrad i) heq
  filter_upwards [hlower] with x hx
  simp only [Sobolev.lowerTruncatedLogSlope, ite_eq_right (not_lt.mpr hx), div_eq_mul_inv, mul_comm]

end HeatKernel

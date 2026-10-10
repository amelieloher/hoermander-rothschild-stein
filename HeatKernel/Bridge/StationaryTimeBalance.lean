-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.StationaryEnergyIdentity
import Mathlib.Tactic

/-! # Scalar time balances obtained from stationary horizontal energy tests -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Fubini turns the space-time stationary energy identity into the scalar weak
time balance. Both the derivative-weighted value and the weighted fluxes are integrable. -/
theorem HasStationaryEnergyTestIdentity.time_balance {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (he : HasStationaryEnergyTestIdentity X a I U u g)
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    (V : Opens (Fin N → ℝ)) (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ J)
    (v : zeroBoundaryGraph V X) :
    Integrable (fun t => deriv ψ t * ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x)
      (volume.restrict J) ∧
    (∀ i, Integrable (fun t => ψ t * ∫ x, (∑ j, a t x i j * g j t x) *
      (v : GradientSpace (N := N) ⊤ q).snd i x) (volume.restrict J)) ∧
    (∫ t in J, deriv ψ t * ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x) =
      ∑ i, ∫ t in J, ψ t * ∫ x, (∑ j, a t x i j * g j t x) *
        (v : GradientSpace (N := N) ⊤ q).snd i x := by
  obtain ⟨hi, hj, hid⟩ := he J K hJ hJI hK hKU V hVK ψ hψ hcψ hsψ v
  have ht : Integrable (fun t => -(deriv ψ t) *
      ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x) (volume.restrict J) := by
    simpa only [mul_assoc, integral_const_mul] using hi.integral_prod_left
  have hf (i : Fin q) : Integrable (fun t => ψ t *
      ∫ x, (∑ j, a t x i j * g j t x) * (v : GradientSpace (N := N) ⊤ q).snd i x)
      (volume.restrict J) := by
    simpa only [mul_assoc, integral_const_mul] using (hj i).integral_prod_left
  refine ⟨?_, hf, ?_⟩
  · simpa only [Pi.neg_def, neg_mul, neg_neg] using ht.neg
  · have hv := integral_prod _ hi
    have hg (i : Fin q) := integral_prod _ (hj i)
    simp only [mul_assoc, integral_const_mul] at hv hg
    simp only [mul_assoc] at hid
    rw [hv] at hid
    simp only [hg, neg_mul, integral_neg] at hid
    linarith

end HeatKernel

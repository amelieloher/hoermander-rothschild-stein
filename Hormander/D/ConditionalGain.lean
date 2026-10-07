-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.LocalizedOrder
public import Hormander.D.C9NormBridge
public import Hormander.Defs.LieWordLength
public import Hormander.Defs.LieWordEval
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open Hormander.Interface
open Hormander.B

namespace Hormander.D

private theorem realMultiplierOperator_tsupport_subset {N : ℕ}
    (η : SchwartzMap (Carrier N) ℝ) (v : TestFunction N) :
    tsupport (realMultiplierOperator η v) ⊆ tsupport (η : Carrier N → ℝ) := by
  have hsmul :
      tsupport ((SchwartzMap.smulLeftCLM ℂ (complexifyRealSchwartz η)) v) ⊆
        tsupport (complexifyRealSchwartz η) := by
    exact (SchwartzMap.tsupport_smulLeftCLM_subset _ _).trans
      (fun _ hx => hx.2)
  have hsupport :
      Function.support (complexifyRealSchwartz η) =
        Function.support (η : Carrier N → ℝ) := by
    ext x
    simp [Function.mem_support, complexifyRealSchwartz]
  have htsupport :
      tsupport (complexifyRealSchwartz η) = tsupport (η : Carrier N → ℝ) := by
    change closure (Function.support (complexifyRealSchwartz η)) =
      closure (Function.support (η : Carrier N → ℝ))
    rw [hsupport]
  change tsupport ((SchwartzMap.smulLeftCLM ℂ (complexifyRealSchwartz η)) v) ⊆ _
  exact hsmul.trans (by rw [htsupport])

/-- Apply a subelliptic estimate to the localized Bessel output, with that estimate supplied as
an explicit hypothesis. -/
theorem applyC9_to_localizedBesselOperator_of_subelliptic_estimate {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (_hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (_hXc : ∀ i, HasCompactSupport (X i))
    (_hc : ContDiff ℝ (⊤ : ℕ∞) c) (_hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (_hK : IsCompact K) (_hU : IsOpen U)
    (_hKU : K ⊆ U) (s : ℕ) (_hs : 1 ≤ s) (w : Fin N → LieWord k)
    (_hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (_hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (hC9 :
      ∃ C : ℝ, ∀ u : 𝓢(EuclideanSpace ℝ (Fin N), ℂ), tsupport u ⊆ K →
        (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 4 ^ s) * ‖𝓕 (⇑u) ξ‖ ^ 2) ≤
          C * ((∫ x, ‖(∑ i : Fin k,
                  fderiv ℝ (fun y => fderiv ℝ u y (X i.succ y)) x (X i.succ x)) +
                fderiv ℝ u x (X 0 x) + (c x : ℂ) * u x‖ ^ 2) +
              ∫ x, ‖u x‖ ^ 2))
    (η₁ η₂ η' : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ))
    (hη₂K : tsupport (η₂ : Carrier N → ℝ) ⊆ K) :
    let A := localizedBesselOperator η₁ η' σ
    ∃ C : ℝ, ∀ u : 𝓢(EuclideanSpace ℝ (Fin N), ℂ),
      (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 4 ^ s) * ‖𝓕 (⇑(A u)) ξ‖ ^ 2) ≤
        C * ((∫ x, ‖(∑ i : Fin k,
                fderiv ℝ (fun y => fderiv ℝ (A u) y (X i.succ y)) x (X i.succ x)) +
              fderiv ℝ (A u) x (X 0 x) + (c x : ℂ) * (A u) x‖ ^ 2) +
            ∫ x, ‖(A u) x‖ ^ 2) := by
  dsimp
  rcases hC9 with ⟨C, hC9⟩
  refine ⟨C, fun u => hC9 ((localizedBesselOperator η₁ η' σ) u) ?_⟩
  have hη'η₂_support : tsupport (η' : Carrier N → ℝ) ⊆
      tsupport (η₂ : Carrier N → ℝ) := by
    intro x hx
    have hη₂one := cutoffPrecedes_eq_one_on_tsupport hη'η₂ hx
    change η₂ x = 1 at hη₂one
    apply subset_tsupport
    simp [hη₂one]
  change tsupport
      (realMultiplierOperator η'
        (lambdaOperator σ (realMultiplierOperator η₁ u))) ⊆ K
  exact (realMultiplierOperator_tsupport_subset η' _).trans
    (hη'η₂_support.trans hη₂K)

end Hormander.D

end

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Extension.Extension

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate FourierTransform

namespace Hormander.B

/-- A real multiplier is its own bilinear transpose. -/
theorem extMultiplier_transpose {N : ℕ} (ζ : SchwartzMap (Carrier N) ℝ) :
    HasBilinearTranspose (realMultiplierOperator ζ) (realMultiplierOperator ζ) := by
  intro u v
  unfold bilinearPairing
  apply integral_congr_ae
  filter_upwards with x
  simp [realMultiplierOperator, multiplierOperator,
    SchwartzMap.smulLeftCLM_apply_apply (complexifyRealSchwartz ζ).hasTemperateGrowth]
  ring

/-- Multiplication of a tempered distribution by a real Schwartz cutoff `ζ`. -/
def cutoffDistr {N : ℕ} (ζ : SchwartzMap (Carrier N) ℝ) : Tempered N →L[ℂ] Tempered N :=
  TemperedDistribution.smulLeftCLM ℂ (⇑(complexifyRealSchwartz ζ))

theorem cutoffDistr_apply_apply {N : ℕ} (ζ : SchwartzMap (Carrier N) ℝ) (u : Tempered N)
    (φ : TestFunction N) : cutoffDistr ζ u φ = u (realMultiplierOperator ζ φ) := rfl

/-- If `T = T ∘ M_ζ` on `𝓢`, then `T^t = M_ζ T^t`. -/
theorem transpose_factor {N : ℕ} {T Tt : Operator N} (hT : HasBilinearTranspose T Tt)
    (ζ : SchwartzMap (Carrier N) ℝ) (hfac : T = T.comp (realMultiplierOperator ζ)) :
    Tt = (realMultiplierOperator ζ).comp Tt := by
  apply LinearMap.ext
  intro φ
  have : Tt φ - (realMultiplierOperator ζ).comp Tt φ = 0 := by
    apply eq_zero_of_bilinearPairing_eq_zero
    intro ψ
    rw [bilinearPairing_comm, bilinearPairing_sub_right]
    have h1 : bilinearPairing ψ (Tt φ) = bilinearPairing (T ψ) φ := (hT ψ φ).symm
    have h2 : bilinearPairing ψ (((realMultiplierOperator ζ).comp Tt) φ) =
        bilinearPairing (T (realMultiplierOperator ζ ψ)) φ := by
      rw [LinearMap.comp_apply, ← (extMultiplier_transpose ζ) ψ (Tt φ), ← hT]
    rw [h1, h2]
    have : T ψ = T (realMultiplierOperator ζ ψ) := by
      conv_lhs => rw [hfac]
      rfl
    rw [this, sub_self]
  exact sub_eq_zero.mp this

/-- If `T = T ∘ M_ζ` then `T' u = T' (ζ u)` for all `u ∈ 𝓢'`. -/
theorem tempExtension_cutoff {N : ℕ} {T Tt : Operator N} (hT : HasBilinearTranspose T Tt)
    (hc : Continuous Tt) (ζ : SchwartzMap (Carrier N) ℝ)
    (hfac : T = T.comp (realMultiplierOperator ζ)) (u : Tempered N) :
    tempExtension Tt hc u = tempExtension Tt hc (cutoffDistr ζ u) := by
  ext φ
  rw [tempExtension_apply_apply, tempExtension_apply_apply, cutoffDistr_apply_apply]
  congr 1
  have := transpose_factor hT ζ hfac
  exact congrArg (fun L : Operator N => L φ) this

/-- Localized estimate on distributions: if `T` has global
order bound `C` at index `r` and `T = T ∘ M_{ζ₂}`, then for every `u ∈ 𝓢'` with
`ζ₂ u ∈ H^{r+m}` (represented by `w`), `T'u = T'(ζ₂ u) ∈ H^r` and
`‖T'u‖_{H^r} ≤ C ‖ζ₂ u‖_{H^{r+m}}`. -/
theorem localized_sobolev_bound {N : ℕ} {T Tt : Operator N} (hT : HasBilinearTranspose T Tt)
    (hc : Continuous Tt) {m r : ℝ} {C : NNReal}
    (hC : ∀ φ : TestFunction N, sobolevNorm r (T φ) ≤ (C : ℝ) * sobolevNorm (r + m) φ)
    (ζ₂ : SchwartzMap (Carrier N) ℝ) (hfac : T = T.comp (realMultiplierOperator ζ₂))
    (u : Tempered N) (w : BesselPotentialSpace (Carrier N) ℂ (r + m) 2)
    (hw : w.toDistr = cutoffDistr ζ₂ u) :
    tempExtension Tt hc u = tempExtension Tt hc w.toDistr ∧
      ∃ v : BesselPotentialSpace (Carrier N) ℂ r 2,
        v.toDistr = tempExtension Tt hc u ∧ ‖v‖ ≤ (C : ℝ) * ‖w‖ := by
  have h1 : tempExtension Tt hc u = tempExtension Tt hc w.toDistr := by
    rw [hw]; exact tempExtension_cutoff hT hc ζ₂ hfac u
  refine ⟨h1, ?_⟩
  obtain ⟨v, hv1, hv2⟩ := tempExtension_sobolev hT hc hC w
  exact ⟨v, by rw [hv1, h1], hv2⟩

end Hormander.B

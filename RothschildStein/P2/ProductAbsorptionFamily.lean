-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.ProductAbsorptionCutoffs

/-!
# The common product absorption for the cutoff family `{ζ, X̃_l ζ, L̃ ζ}`

The product absorption estimate (BB p. 592 (11.75)–(11.80); p. 601 (11.92)), assembled from
`ProductAbsorption.product_absorption` (the finite-family absorption with one common flow time) and
`exists_radialCutoffBounds_of_smooth_cutoffs_drift` (the bounds of the radial cutoff construction for the family
`ℬ = {ζ, X̃_l ζ (1 ≤ l ≤ q), L̃ ζ}` of weights `d_b = 0, 1, 2`):

`‖uζ‖ + ∑_l ‖u X̃_l ζ‖ + ‖u L̃ ζ‖ ≤ ε M + C a^{-2} D + C ε^{-2/α} a^{-(2+8/α)} U`

in the `C^α(B)` norm of the supporting control ball `B`, with `C` independent of `u, ζ, a, ε`.
`exists_radialCutoffBounds_of_smooth_cutoffs_drift` repackages the conclusion of
`RothschildStein.P2.smooth_cutoffs_drift` (the lifted chart, a smooth gauge `ν`) as the hypothesis
`RadialCutoffBounds` of the family theorem, with one set of word constants and `a = r - s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P2

open RothschildStein.P1

section Chart

variable {n q st m : ℕ}

/-- The word constants of the radial cutoff construction can be taken `≤ C_b` on the finitely many words of length `≤ 4`. -/
theorem exists_bound_on_short_words (c : List (Fin (q + 1)) → ℝ) :
    ∃ Cb0 : ℝ, ∀ I : List (Fin (q + 1)), I.length ≤ 4 → c I ≤ Cb0 := by
  obtain ⟨b, hb⟩ := ((List.finite_length_le (Fin (q + 1)) 4).image c).bddAbove
  exact ⟨b, fun I hI => hb ⟨I, hI, rfl⟩⟩

/-- The conclusion of `smooth_cutoffs_drift` in the form used by the product absorption:
one threshold `r_*`, one set of word constants `c I ≥ 0` (a single bound `C_b` for all words of
length at most four) such that for every centre `ξ₀ ∈ Kc` and `0 < s < r < r_*` the radial cutoff
`φ` is smooth with compact support, `tsupport φ ⊆ closedRhoBall ((s + r)/2)`, and for every
`α ∈ (0, 1)` the hypotheses `RadialCutoffBounds` hold at the scale `a = r - s`. -/
theorem exists_radialCutoffBounds_of_smooth_cutoffs_drift {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : LiftedChart driftWeight st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth)
    {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U) :
    ∃ rstar : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧ ∃ (c : List (Fin (q + 1)) → ℝ) (Cb0 : ℝ),
      (∀ I : List (Fin (q + 1)), I.length ≤ 4 → c I ≤ Cb0) ∧
      ∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r → r < rstar →
        (ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ s r) ∧
          HasCompactSupport (radialCutoff C ν ξ₀ s r) ∧
          (∀ ξ, 0 ≤ radialCutoff C ν ξ₀ s r ξ ∧ radialCutoff C ν ξ₀ s r ξ ≤ 1) ∧
          EqOn (radialCutoff C ν ξ₀ s r) (fun _ => 1) (rhoBall C ν ξ₀ s) ∧
          tsupport (radialCutoff C ν ξ₀ s r) ⊆ closedRhoBall C ν ξ₀ ((s + r) / 2) ∧
          closedRhoBall C ν ξ₀ ((s + r) / 2) ⊆ rhoBall C ν ξ₀ r) ∧
        ∀ α : ℝ, 0 < α → α < 1 →
          RadialCutoffBounds C.Xl C.O α (r - s) (radialCutoff C ν ξ₀ s r) c := by
  obtain ⟨rstar, hr0, hr1, hqual, hsup, hhol⟩ := smooth_cutoffs_drift C ν hν hKc hKU
  choose c1 hc1 hc1b using hsup
  choose c2 hc2 hc2b using hhol
  obtain ⟨Cb0, hCb0⟩ := exists_bound_on_short_words (fun I => max (c1 I) (c2 I))
  refine ⟨rstar, hr0, hr1, fun I => max (c1 I) (c2 I), Cb0, hCb0, ?_⟩
  intro ξ₀ hξ₀ s r hs hsr hr
  refine ⟨hqual ξ₀ hξ₀ s r hs hsr hr, fun α hα0 hα1 => ?_⟩
  have ha : 0 < r - s := sub_pos.2 hsr
  have hzpow : ∀ e : ℤ, 0 ≤ (r - s) ^ e := fun e => zpow_nonneg ha.le e
  refine ⟨fun I => (hc1 I).trans (le_max_left _ _), fun I ξ => ?_, fun I => ?_⟩
  · exact (hc1b I ξ₀ hξ₀ s r hs hsr hr ξ).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hzpow _))
  · exact (hc2b I ξ₀ hξ₀ s r hs hsr hr α hα0 hα1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) (hzpow _)))

end Chart

variable {n q : ℕ}

end RothschildStein.P2

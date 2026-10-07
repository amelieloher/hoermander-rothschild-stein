-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLiePointMaps
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

theorem generalLieSinglePointMap_contDiffAt {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) {ε : ℝ} {x : Fin N → ℝ}
    (hε : 0 < ε)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x ε) ×ˢ Ioo (-2) 2)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
      finiteLieTimeOneMap Φ (dilatedInputCoordinates D f q.1,q.2)) (0,x) := by
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
      (dilatedInputCoordinates D f q.1,q.2)) :=
    ((dilatedInputCoordinates_contDiff D f).comp contDiff_fst).prodMk contDiff_snd
  exact exponential_map_contDiffAt_of_input hε hi.contDiffAt
    (by simp only [dilatedInputCoordinates_zero]) hΦ

theorem generalLiePointMaps_contDiffAt {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f g : formalSpan a s p) {ε : ℝ} {x : Fin N → ℝ}
    (hε : 0 < ε)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x ε) ×ˢ Ioo (-2) 2))
    (hzero : finiteLieTimeOneMap Φ (0,x) = x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
      generalLieSuccessivePointMap D Φ f g q.1 q.2) (0,x) ∧
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
      generalLieBCHPointMap D Φ f g q.1 q.2) (0,x) := by
  refine ⟨?_,generalLieSinglePointMap_contDiffAt D (modelProduct f g) hε Φ hΦ⟩
  have hf := generalLieSinglePointMap_contDiffAt D f hε Φ hΦ
  have hi := ((dilatedInputCoordinates_contDiff D g).comp contDiff_fst).contDiffAt.prodMk hf
  have hb : (dilatedInputCoordinates D g (0 : ℝ),
      finiteLieTimeOneMap Φ (dilatedInputCoordinates D f 0,x)) = (0,x) := by
    rw [dilatedInputCoordinates_zero,dilatedInputCoordinates_zero,hzero]
  exact exponential_map_contDiffAt_of_input hε hi hb hΦ
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLiePointLists
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- Restriction of the actual joint list identity to its scalar scale parameter. -/
theorem retainedLiePointList_scalar_jets_eq_product {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {ε : ℝ} {x : Fin N → ℝ} (hε : 0 < ε)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x ε) ×ˢ Ioo (-2) 2))
    (hzero : ∀ y ∈ ball x ε, finiteLieTimeOneMap Φ (0,y) = y)
    (hj : ∀ f g : formalSpan a s p, ∀ k ≤ s,
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        generalLieSuccessivePointMap D Φ f g q.1 (x+q.2)) 0 =
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        generalLieBCHPointMap D Φ f g q.1 (x+q.2)) 0)
    (fs : List (formalSpan a s p))
    (hfs : ContDiffAt ℝ s (fun q : ℝ × (Fin N → ℝ) =>
      runRetainedLiePointList D Φ fs q.1 (x+q.2)) 0) : ∀ k ≤ s,
    iteratedFDeriv ℝ k (fun t => runRetainedLiePointList D Φ fs t x) 0 =
      iteratedFDeriv ℝ k (fun t => finiteLieTimeOneMap Φ
        (dilatedInputCoordinates D (retainedLieListProduct fs) t,x)) 0 := by
  let H := fun q : ℝ × (Fin N → ℝ) => (q.1,x+q.2)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := contDiff_fst.prodMk (contDiff_const.add contDiff_snd)
  have hpoint : H 0 = (0,x) := by change (0,x+0) = (0,x); rw [add_zero]
  have he : ContDiffAt ℝ s (fun q : ℝ × (Fin N → ℝ) => finiteLieTimeOneMap Φ
      (dilatedInputCoordinates D (retainedLieListProduct fs) q.1,x+q.2)) 0 := by
    have hh := generalLieSinglePointMap_contDiffAt D (retainedLieListProduct fs) hε Φ hΦ
    rw [← hpoint] at hh
    exact (hh.comp 0 hH.contDiffAt).of_le (by simp)
  have h := frechet_jets_substitution_eq
    (h := fun t : ℝ => (t,(0 : Fin N → ℝ)))
    (contDiffAt_id.prodMk contDiffAt_const) rfl hfs he
    (retainedLiePointList_jets_eq_product_of_joint_jets D hε Φ hΦ hzero hj fs)
  simpa only [Function.comp_def,add_zero] using h
end RothschildStein.G3

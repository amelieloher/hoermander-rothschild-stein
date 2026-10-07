-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLiePointMapSmoothness
public import RothschildStein.G3.RadialFlatFrechetJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import RothschildStein.G3.ParameterStateJetLift
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

theorem generalLie_shifted_pointMaps_contDiffAt {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f g : formalSpan a s p) {ε : ℝ} {x : Fin N → ℝ}
    (hε : 0 < ε)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x ε) ×ˢ Ioo (-2) 2))
    (hzero : finiteLieTimeOneMap Φ (0,x) = x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
      generalLieSuccessivePointMap D Φ f g q.1 (x+q.2)) 0 ∧
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
      generalLieBCHPointMap D Φ f g q.1 (x+q.2)) 0 := by
  have hj := generalLiePointMaps_contDiffAt D f g hε Φ hΦ hzero
  let H : ℝ × (Fin N → ℝ) → ℝ × (Fin N → ℝ) := fun q => (q.1,x+q.2)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := contDiff_fst.prodMk (contDiff_const.add contDiff_snd)
  have hH0 : H 0 = (0,x) := by change ((0 : ℝ),x+0) = (0,x); rw [add_zero]
  constructor
  · have hf : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
        generalLieSuccessivePointMap D Φ f g q.1 q.2) (H 0) := by rw [hH0]; exact hj.1
    exact hf.comp 0 hH.contDiffAt
  · have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
        generalLieBCHPointMap D Φ f g q.1 q.2) (H 0) := by rw [hH0]; exact hj.2
    exact hg.comp 0 hH.contDiffAt

end RothschildStein.G3

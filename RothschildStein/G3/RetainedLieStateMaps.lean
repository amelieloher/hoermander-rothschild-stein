-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLieStateCompositionJets
@[expose] public section
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.G3

def retainedLieStateMap {a s N : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (f : formalSpan a s p) : ℝ × (Fin N → ℝ) → ℝ × (Fin N → ℝ) :=
  parameterStateLift x (fun q => finiteLieTimeOneMap Φ (dilatedInputCoordinates D f q.1,x+q.2))

theorem retainedLieStateMap_contDiffAt {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) {ε : ℝ} {x : Fin N → ℝ}
    (hε : 0 < ε)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x ε) ×ˢ Ioo (-2) 2)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (retainedLieStateMap D Φ x f) 0 := by
  let H : ℝ × (Fin N → ℝ) → ℝ × (Fin N → ℝ) := fun q => (q.1,x+q.2)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := contDiff_fst.prodMk (contDiff_const.add contDiff_snd)
  have hh : H 0 = (0,x) := by change ((0 : ℝ),x+0) = (0,x); rw [add_zero]
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
      finiteLieTimeOneMap Φ (dilatedInputCoordinates D f q.1,q.2)) (H 0) := by
    rw [hh]; exact generalLieSinglePointMap_contDiffAt D f hε Φ hΦ
  have he := hf.comp 0 hH.contDiffAt
  exact contDiffAt_fst.prodMk (he.sub contDiffAt_const)

theorem retainedLieStateMap_zero {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (hzero : finiteLieTimeOneMap Φ (0,x) = x) :
    retainedLieStateMap D Φ x f 0 = 0 := by
  apply parameterStateLift_zero
  simp only [Prod.fst_zero,Prod.snd_zero,add_zero,dilatedInputCoordinates_zero,hzero]

theorem retainedLieStateMap_comp {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f g : formalSpan a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) :
    retainedLieStateMap D Φ x g ∘ retainedLieStateMap D Φ x f =
      parameterStateLift x (fun q => generalLieSuccessivePointMap D Φ f g q.1 (x+q.2)) := by
  funext q
  have he : x+(finiteLieTimeOneMap Φ (dilatedInputCoordinates D f q.1,x+q.2)-x) =
      finiteLieTimeOneMap Φ (dilatedInputCoordinates D f q.1,x+q.2) := by abel
  simp only [Function.comp_apply,retainedLieStateMap,parameterStateLift,generalLieSuccessivePointMap,he]

theorem retainedLieStateMap_zeroInput_eventuallyEq_id {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {ε : ℝ} (hε : 0 < ε)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (hzero : ∀ y ∈ ball x ε, finiteLieTimeOneMap Φ (0,y) = y) :
    retainedLieStateMap D Φ x 0 =ᶠ[𝓝 0] id := by
  have hy : ∀ᶠ q : ℝ × (Fin N → ℝ) in 𝓝 0, x+q.2 ∈ ball x ε := by
    have ht := (show Continuous (fun q : ℝ × (Fin N → ℝ) => x+q.2) by fun_prop).tendsto 0
    have ht' : Tendsto (fun q : ℝ × (Fin N → ℝ) => x+q.2) (𝓝 0) (𝓝 x) := by simpa using ht
    exact ht'.eventually (isOpen_ball.mem_nhds (by simpa using hε))
  filter_upwards [hy] with q hq
  have hc : dilatedInputCoordinates D (0 : formalSpan a s p) q.1 = 0 := by
    funext j
    simp [dilatedInputCoordinates,coordinateDilation]
  simp only [retainedLieStateMap,parameterStateLift,hc,hzero _ hq,id_eq]
  congr 1
  abel
end RothschildStein.G3

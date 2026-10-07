-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLieListJets
public import RothschildStein.G3.ParameterStateJetProjection
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G3

def runRetainedLiePointList {a s N : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ)) :
    List (formalSpan a s p) → ℝ → (Fin N → ℝ) → (Fin N → ℝ)
  | [],_,y => y
  | f :: fs,δ,y => runRetainedLiePointList D Φ fs δ
      (finiteLieTimeOneMap Φ (dilatedInputCoordinates D f δ,y))

theorem chronological_retainedLieStateMap_apply {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (fs : List (formalSpan a s p)) (δ : ℝ) (y : Fin N → ℝ) :
    chronologicalComposition (fs.map (retainedLieStateMap D Φ x)) (δ,y-x) =
      (δ,runRetainedLiePointList D Φ fs δ y-x) := by
  induction fs generalizing y with
  | nil => rfl
  | cons f fs ih =>
    have hy : x+(y-x) = y := by abel
    simp only [List.map_cons,chronologicalComposition,Function.comp_apply,
      retainedLieStateMap,parameterStateLift,hy,runRetainedLiePointList]
    exact ih _

theorem chronological_retainedLieStateMap_eq_lift {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (fs : List (formalSpan a s p)) :
    chronologicalComposition (fs.map (retainedLieStateMap D Φ x)) =
      parameterStateLift x (fun q => runRetainedLiePointList D Φ fs q.1 (x+q.2)) := by
  funext q
  have he := chronological_retainedLieStateMap_apply D Φ x fs q.1 (x+q.2)
  simpa only [add_sub_cancel_left,parameterStateLift] using he
theorem runRetainedLiePointList_zero {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (hzero : finiteLieTimeOneMap Φ (0,x) = x)
    (fs : List (formalSpan a s p)) : runRetainedLiePointList D Φ fs 0 x = x := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [runRetainedLiePointList,dilatedInputCoordinates_zero,hzero,ih]

theorem retainedLiePointList_jets_eq_product_of_joint_jets {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {ε : ℝ} {x : Fin N → ℝ} (hε : 0 < ε)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((Metric.ball 0 ε ×ˢ Metric.ball x ε) ×ˢ Set.Ioo (-2) 2))
    (hzero : ∀ y ∈ Metric.ball x ε, finiteLieTimeOneMap Φ (0,y) = y)
    (hj : ∀ f g : formalSpan a s p, ∀ k ≤ s,
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        generalLieSuccessivePointMap D Φ f g q.1 (x+q.2)) 0 =
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        generalLieBCHPointMap D Φ f g q.1 (x+q.2)) 0)
    (fs : List (formalSpan a s p)) : ∀ k ≤ s,
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        runRetainedLiePointList D Φ fs q.1 (x+q.2)) 0 =
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        finiteLieTimeOneMap Φ (dilatedInputCoordinates D (retainedLieListProduct fs) q.1,x+q.2)) 0 := by
  have hz : finiteLieTimeOneMap Φ (0,x) = x := hzero x (by simpa using hε)
  have hs : ContDiffAt ℝ s (chronologicalComposition (fs.map (retainedLieStateMap D Φ x))) 0 := by
    apply chronologicalComposition_contDiffAt
    · intro f hf
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hf
      exact (retainedLieStateMap_contDiffAt D a hε Φ hΦ).of_le (by simp)
    · intro f hf
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hf
      exact retainedLieStateMap_zero D a Φ x hz
  rw [chronological_retainedLieStateMap_eq_lift] at hs
  apply point_jets_eq_of_parameterStateLift_jets_eq hs
    ((retainedLieStateMap_contDiffAt D (retainedLieListProduct fs) hε Φ hΦ).of_le (by simp))
  · simpa only [Prod.fst_zero,Prod.snd_zero,add_zero] using runRetainedLiePointList_zero D Φ x hz fs
  · change finiteLieTimeOneMap Φ (dilatedInputCoordinates D (retainedLieListProduct fs) 0,x+0) = x
    rw [add_zero,dilatedInputCoordinates_zero D (retainedLieListProduct fs),hz]
  · have he := retainedLieList_jets_eq_product_of_joint_jets D hε Φ hΦ hzero hj fs
    rw [chronological_retainedLieStateMap_eq_lift] at he
    exact he
end RothschildStein.G3

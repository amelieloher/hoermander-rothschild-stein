-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLieStateMaps
public import RothschildStein.G3.ChronologicalCompositionJets
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- BCH product exposed on the fixed formal-span carrier. -/
def retainedLieProduct {a s : ℕ} {p : Fin a → ℕ+}
    (f g : formalSpan a s p) : formalSpan a s p := modelProduct f g

theorem retainedLieProduct_assoc {a s : ℕ} {p : Fin a → ℕ+}
    (f g h : formalSpan a s p) :
    retainedLieProduct (retainedLieProduct f g) h = retainedLieProduct f (retainedLieProduct g h) :=
  modelProduct_assoc f g h

@[simp] theorem retainedLieProduct_zero_left {a s : ℕ} {p : Fin a → ℕ+}
    (f : formalSpan a s p) : retainedLieProduct 0 f = f := modelProduct_zero_left f

@[simp] theorem retainedLieProduct_zero_right {a s : ℕ} {p : Fin a → ℕ+}
    (f : formalSpan a s p) : retainedLieProduct f 0 = f := modelProduct_zero_right f

@[simp] theorem retainedLieProduct_neg_left {a s : ℕ} {p : Fin a → ℕ+}
    (f : formalSpan a s p) : retainedLieProduct (-f) f = 0 := modelProduct_neg_left f

@[simp] theorem retainedLieProduct_neg_right {a s : ℕ} {p : Fin a → ℕ+}
    (f : formalSpan a s p) : retainedLieProduct f (-f) = 0 := modelProduct_neg_right f

def retainedLieListProduct {a s : ℕ} {p : Fin a → ℕ+}
    (fs : List (formalSpan a s p)) : formalSpan a s p := fs.foldr retainedLieProduct 0

/-- Actual finite retained-Lie flow lists have the jets of their single formal
BCH product, on the same family. The hypothesis is the shared pairwise jet API. -/
theorem retainedLieList_jets_eq_product_of_joint_jets {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {ε : ℝ} {x : Fin N → ℝ} (hε : 0 < ε)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x ε) ×ˢ Ioo (-2) 2))
    (hzero : ∀ y ∈ ball x ε, finiteLieTimeOneMap Φ (0,y) = y)
    (hj : ∀ f g : formalSpan a s p, ∀ k ≤ s,
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        generalLieSuccessivePointMap D Φ f g q.1 (x+q.2)) 0 =
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        generalLieBCHPointMap D Φ f g q.1 (x+q.2)) 0)
    (fs : List (formalSpan a s p)) : ∀ k ≤ s,
      iteratedFDeriv ℝ k (chronologicalComposition (fs.map (retainedLieStateMap D Φ x))) 0 =
        iteratedFDeriv ℝ k (retainedLieStateMap D Φ x (retainedLieListProduct fs)) 0 := by
  have hz : finiteLieTimeOneMap Φ (0,x) = x := hzero x (by simpa using hε)
  apply chronologicalComposition_jets_eq_product retainedLieProduct (retainedLieStateMap D Φ x)
  · intro f
    exact (retainedLieStateMap_contDiffAt D f hε Φ hΦ).of_le (by simp)
  · intro f
    exact retainedLieStateMap_zero D f Φ x hz
  · intro k _
    exact ((retainedLieStateMap_zeroInput_eventuallyEq_id D hε Φ x hzero).iteratedFDeriv ℝ k).eq_of_nhds
  · intro f g
    rw [retainedLieStateMap_comp D f g Φ x]
    have hs := generalLie_shifted_pointMaps_contDiffAt D f g hε Φ hΦ hz
    exact parameterStateLift_jets_eq (hs.1.of_le (by simp)) (hs.2.of_le (by simp)) (hj f g)
end RothschildStein.G3

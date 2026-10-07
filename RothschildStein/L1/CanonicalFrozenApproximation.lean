-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameFullWeight
public import RothschildStein.L1.CanonicalWordBasisExpansion
public import RothschildStein.L1.HomogeneousWordCoordinates
public import RothschildStein.L1.WeightedFieldLocality
public import RothschildStein.L1.CoordinateFieldJetClasses
public import RothschildStein.L1.CanonicalWordRemainderFullWeight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The canonical word remainder satisfies the exact
integer weighted-jet predicate (BB Theorem 10.28, pp. 506–509). -/
theorem canonicalWordRemainder_weightedJet {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (I : List (Fin a)) :
    WeightedJet D.weight (1 - (wordWeight p I : ℤ))
      (fun u => canonicalWordRemainder D X C I (η,u)) := by
  apply (fieldJetVanishing_all_iff_WeightedJet D.weight _ _).mp
  intro q
  have hh := (canonical_word_remainder_full_weight D Ω X hX C η hη I q).2
  simpa only [Int.cast_sub,Int.cast_one,Int.cast_natCast] using hh

end RothschildStein.L1

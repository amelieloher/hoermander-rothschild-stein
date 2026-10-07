-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CanonicalLocalApproximation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The scalar action identity also yields the exact vector identity
required by the chart, for every word on the same patch
(BB Theorem 10.30, pp. 510–511). -/
theorem canonicalWordRemainder_vector_identity {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    {η ξ : Fin (freeDimension a s p) → ℝ}
    (hη : η ∈ ball x C.radius) (hξ : ξ ∈ ball x C.radius)
    (hu : C.theta (η,ξ) ∈ ball 0 C.radius) (I : List (Fin a)) :
    fderiv ℝ (fun z => C.theta (η,z)) ξ (wordBracket X I ξ) =
      wordBracket D.fields I (C.theta (η,ξ)) +
        canonicalWordRemainder D X C I (η,C.theta (η,ξ)) := by
  have hp := C.pullbackField_wordBracket Ω.isOpen X hX η hη I _ hu
  have hi := C.right_inverse (η,ξ) (C.basePatch_subset ⟨hη,hξ⟩)
  change canonicalFrameMap C.time C.flow (η,C.theta (η,ξ)) = ξ at hi
  unfold CanonicalFrameChartData.pullbackField at hp
  rw [hi] at hp
  rw [hp]
  unfold canonicalWordRemainder
  abel

end RothschildStein.L1

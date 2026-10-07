-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalWordRemainder
public import RothschildStein.L1.CanonicalActionIdentity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The actual original word acts in canonical
coordinates as the model word plus the actual remainder field. -/
theorem canonicalWordRemainder_action {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η ξ : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (hq : (η,ξ) ∈ C.inverseDomain) (hu : C.theta (η,ξ) ∈ ball 0 C.radius)
    (I : List (Fin a)) (f : (Fin (freeDimension a s p) → ℝ) → ℝ)
    (hf : DifferentiableAt ℝ f (C.theta (η,ξ))) :
    fieldDerivative (wordBracket X I) (fun z => f (C.theta (η,z))) ξ =
      fieldDerivative (wordBracket D.fields I) f (C.theta (η,ξ)) +
        fderiv ℝ f (C.theta (η,ξ)) (canonicalWordRemainder D X C I (η,C.theta (η,ξ))) := by
  rw [C.pullbackField_action η ξ hq (wordBracket X I) f hf]
  unfold fieldDerivative
  rw [C.pullbackField_wordBracket Ω.isOpen X hX η hη I _ hu]
  simp only [canonicalWordRemainder, map_sub]
  abel
end RothschildStein.L1

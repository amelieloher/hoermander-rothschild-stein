-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrozenApproximation
public import RothschildStein.L1.CanonicalRemainderAction
public import RothschildStein.L1.CanonicalInverseIdentity
public import RothschildStein.L1.CanonicalCompleteDensity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The local approximation data on one fixed canonical coefficient
patch. The zero-value claim is restricted to retained words. -/
structure CanonicalLocalApproximationProperties {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x) : Prop where
  smooth : ∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (canonicalWordRemainder D X C I)
    (ball x C.radius ×ˢ ball 0 C.radius)
  weight : ∀ η ∈ ball x C.radius, ∀ I,
    fullFieldJetClass (ball 0 C.radius) D.weight (1 - (wordWeight p I : ℝ))
      (fun u => canonicalWordRemainder D X C I (η,u))
  frozen_weight : ∀ η ∈ ball x C.radius, ∀ I,
    WeightedJet D.weight (1 - (wordWeight p I : ℤ))
      (fun u => canonicalWordRemainder D X C I (η,u))
  zero : ∀ η ∈ ball x C.radius, ∀ I, wordWeight p I ≤ s →
    canonicalWordRemainder D X C I (η,0) = 0
  action : ∀ η ξ, η ∈ ball x C.radius → (η,ξ) ∈ C.inverseDomain →
    C.theta (η,ξ) ∈ ball 0 C.radius → ∀ I f,
    DifferentiableAt ℝ f (C.theta (η,ξ)) →
      fieldDerivative (wordBracket X I) (fun z => f (C.theta (η,z))) ξ =
        fieldDerivative (wordBracket D.fields I) f (C.theta (η,ξ)) +
          fderiv ℝ f (C.theta (η,ξ))
            (canonicalWordRemainder D X C I (η,C.theta (η,ξ)))
  inverse : ∀ η ξ, (η,ξ) ∈ C.inverseDomain →
    D.group.inv (C.theta (η,ξ)) = C.theta (ξ,η) ∧
      C.theta (ξ,η) = -C.theta (η,ξ)
  forward_density : C.PositiveDensityProperties C.forwardDensity
  first_density : C.PositiveDensityProperties C.firstVariableDensity

/-- Jointly smooth actual remainders of strict word weight,
the exact action identity, corrected model inverse, and both positive
normalized Lebesgue densities hold on the constructed common patch
(BB Theorem 10.30 and Proposition 10.33, pp. 510–513). -/
theorem canonical_local_approximation {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x) :
    CanonicalLocalApproximationProperties D Ω X C := by
  have hY := fun k => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D k)
  exact {
    smooth := canonicalWordRemainder_contDiffOn D Ω X hX C
    weight := fun η hη I => canonical_word_remainder_full_weight D Ω X hX C η hη I
    frozen_weight := fun η hη I => canonicalWordRemainder_weightedJet D Ω X hX C η hη I
    zero := fun η hη I hI => canonicalWordRemainder_zero D Ω X hX C η hη I hI
    action := fun η ξ hη hq hu I f hf => canonicalWordRemainder_action D Ω X hX C
      η ξ hη hq hu I f hf
    inverse := canonicalTheta_inverse_identity D X C
    forward_density := C.forward_positive_density_properties Ω.isOpen hY
    first_density := C.first_positive_density_properties Ω.isOpen hY
  }
/-- A smooth free system constructs the common canonical
chart and the complete local approximation data
(BB Theorems 10.28–10.30, pp. 506–511). -/
theorem exists_free_canonical_local_approximation {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (x : Fin (freeDimension a s p) → ℝ) (hx : x ∈ Ω) (hfree : FreeAt p s X x) :
    ∃ C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x,
      CanonicalLocalApproximationProperties D Ω X C := by
  obtain ⟨C⟩ := nonempty_freeCanonicalFrameChartData D Ω X hX x hx hfree
  exact ⟨C,canonical_local_approximation D Ω X hX C⟩

end RothschildStein.L1

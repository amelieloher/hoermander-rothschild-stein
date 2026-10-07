-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicDilation
public import RothschildStein.H1.Standing
public import RothschildStein.G2.TransposeHomogeneity
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H3

/-- Actual dilation of a global compact intrinsic jet family.
Each word receives its weighted power; no scalar differentiability
hypothesis is needed (BB Corollary 8.51, p. 380). -/
theorem compact_intrinsic_jets_dilate {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    {R : ℝ} (hR : 0 < R) (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 →
      hasIntrinsicWordDeriv H.fields ⊤ I f (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I)) :
    let scaled := fun I x => R ^ (wordWeight driftWeight I : ℝ) * jet I (G.dilate R x)
    scaled [] = f ∘ G.dilate R ∧
      (∀ I, wordWeight driftWeight I ≤ 2 →
        hasIntrinsicWordDeriv H.fields ⊤ I (f ∘ G.dilate R) (scaled I)) ∧
      (∀ I, wordWeight driftWeight I ≤ 2 → Continuous (scaled I)) ∧
      (∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (scaled I)) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x
    simp [wordWeight, hzero, Function.comp_apply]
  · intro I hI
    have hh (i : Fin (q + 1)) :
        G2.IsHomogeneousField G (H.fields i) ((driftWeight i : ℕ) : ℝ) := by
      by_cases hz : i = 0
      · simpa [driftWeight, hz] using H.homogeneous i
      · simpa [driftWeight, hz] using H.homogeneous i
    have hd := hasIntrinsicWordDeriv_dilate G ⊤ driftWeight H.fields
      (H.fields_smooth G) hh hR I (hi I hI)
    have he : (⟨G.dilate R ⁻¹' ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)),
        (⊤ : Opens (Fin N → ℝ)).isOpen.preimage (G2.contDiff_dilate G R).continuous⟩ :
        Opens (Fin N → ℝ)) = ⊤ := by
      ext x
      simp
    rwa [he] at hd
  · intro I hI
    exact continuous_const.mul ((hc I hI).comp (G2.contDiff_dilate G R).continuous)
  · intro I hI
    have hh := (hs I hI).comp_homeomorph (G2.dilationHomeomorph G R hR)
    have hc := HasCompactSupport.smul_left (f := fun _ : Fin N → ℝ =>
      R ^ (wordWeight driftWeight I : ℝ)) hh
    have he : ((fun _ : Fin N → ℝ => R ^ (wordWeight driftWeight I : ℝ)) •
        (jet I ∘ G2.dilationHomeomorph G R hR)) =
        (fun x => R ^ (wordWeight driftWeight I : ℝ) * jet I (G.dilate R x)) := by
      funext x
      rfl
    exact he ▸ hc

/-- The drift and every horizontal square have weight two,
so their actual sum has one common quadratic dilation factor. -/
theorem intrinsic_jet_source_dilate {N q : ℕ} (G : HomogeneousGroup N)
    (R : ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    R ^ (wordWeight (driftWeight (q := q)) [0] : ℝ) * jet [0] (G.dilate R x) +
      ∑ i : Fin q, R ^ (wordWeight driftWeight [i.succ, i.succ] : ℝ) *
        jet [i.succ, i.succ] (G.dilate R x) =
    R ^ 2 * (jet [0] (G.dilate R x) +
      ∑ i : Fin q, jet [i.succ, i.succ] (G.dilate R x)) := by
  simp [wordWeight, driftWeight, mul_add, Finset.mul_sum]

end RothschildStein.H3

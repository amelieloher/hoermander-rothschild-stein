-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.Truncation
public import RothschildStein.G2.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Strong shell cancellation holds without an upper restriction on the
radii (BB Lemma 8.24, pp. 354–356). -/
theorem truncatedKernel_shell_zero_of_radial_shells
    (ν f : (Fin N → ℝ) → ℝ)
    (hshell : ∀ a b : ℝ, 0 < a → a < b → ∀ Φ : ℝ → ℝ,
      ContinuousOn Φ (Icc a b) →
        (∫ w in {w | a < ν w ∧ ν w < b}, f w * Φ (ν w)) = 0)
    (x : Fin N → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ y in {y | a < gaugeDistance G ν x y ∧ gaugeDistance G ν x y < b},
      truncatedKernel G ν f x y) = 0 := by
  have hm := (measurePreserving_rightTranslation G x).comp (measurePreserving_inv G)
  have he := hm.measurable.measurableEmbedding
    ((rightTranslation_bijective G x).comp (inv_bijective G)).injective
  have hi := (hm.restrict_preimage_emb he {w | a < ν w ∧ ν w < b}).integral_comp he
    (fun w => f w * radialCutoff (ν w))
  have heq :
      (∫ y in {y | a < gaugeDistance G ν x y ∧ gaugeDistance G ν x y < b},
        truncatedKernel G ν f x y) =
      ∫ w in {w | a < ν w ∧ ν w < b}, f w * radialCutoff (ν w) := by
    simpa only [Set.preimage_ofPred_eq, Function.comp_def,
      truncatedKernel, gaugeDistance] using hi
  rw [heq]
  exact hshell a b ha hab radialCutoff radialCutoff_lipschitz.continuous.continuousOn

end RothschildStein.H3

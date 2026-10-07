-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLieAbsoluteLists
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

theorem retainedLiePointList_contDiffAt_of_bounds {a s N Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (fs : List (formalSpan a s p)) (q : ℝ × (Fin N → ℝ)) {B : ℝ}
    (h : ChronologicalJetBounds Q B (fs.map (retainedLieAbsoluteStateMap D Φ)) q) :
    ContDiffAt ℝ Q (fun w : ℝ × (Fin N → ℝ) =>
      runRetainedLiePointList D Φ fs w.1 w.2) q := by
  have he : (fun w : ℝ × (Fin N → ℝ) => runRetainedLiePointList D Φ fs w.1 w.2) =
      Prod.snd ∘ chronologicalComposition (fs.map (retainedLieAbsoluteStateMap D Φ)) := by
    funext w
    exact congrArg Prod.snd (chronological_retainedLieAbsoluteStateMap D Φ fs w.1 w.2).symm
  rw [he]
  exact contDiffAt_snd.comp q (chronologicalComposition_contDiffAt_of_bounds Q B _ q h)

theorem retainedLiePointList_parameter_contDiffAt_of_bounds {a s N Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (fs : List (formalSpan a s p)) (t : ℝ) (x : Fin N → ℝ) {B : ℝ}
    (h : ChronologicalJetBounds Q B (fs.map (retainedLieAbsoluteStateMap D Φ)) (t,x)) :
    ContDiffAt ℝ Q (fun v => runRetainedLiePointList D Φ fs v x) t := by
  exact (retainedLiePointList_contDiffAt_of_bounds D Φ fs (t,x) h).comp
    (f := fun v : ℝ => (v,x)) t (contDiffAt_id.prodMk contDiffAt_const)
end RothschildStein.G3

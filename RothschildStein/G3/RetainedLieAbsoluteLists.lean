-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLiePositiveJets
public import RothschildStein.G3.ChronologicalJetBounds
public import RothschildStein.G3.RetainedLiePointLists
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

theorem chronological_retainedLieAbsoluteStateMap {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (fs : List (formalSpan a s p)) (t : ℝ) (x : Fin N → ℝ) :
    chronologicalComposition (fs.map (retainedLieAbsoluteStateMap D Φ)) (t,x) =
      (t,runRetainedLiePointList D Φ fs t x) := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    change chronologicalComposition (fs.map (retainedLieAbsoluteStateMap D Φ))
      (t,finiteLieTimeOneMap Φ (dilatedInputCoordinates D f t,x)) = _
    exact ih _

/-- State projection of the chronological update does not increase joint jets. -/
theorem norm_retainedLiePointList_joint_jet_le {a s N Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (fs : List (formalSpan a s p)) (q : ℝ × (Fin N → ℝ))
    {B : ℝ} (hB : 1 ≤ B)
    (h : ChronologicalJetBounds Q B (fs.map (retainedLieAbsoluteStateMap D Φ)) q)
    (j : ℕ) (hj : 1 ≤ j) (hjQ : j ≤ Q) :
    ‖iteratedFDeriv ℝ j (fun w : ℝ × (Fin N → ℝ) =>
      runRetainedLiePointList D Φ fs w.1 w.2) q‖ ≤ chronologicalJetBudget Q B fs.length := by
  let F := chronologicalComposition (fs.map (retainedLieAbsoluteStateMap D Φ))
  let L := ContinuousLinearMap.snd ℝ ℝ (Fin N → ℝ)
  have hF : ContDiffAt ℝ Q F q := chronologicalComposition_contDiffAt_of_bounds Q B _ q h
  have he : (fun w : ℝ × (Fin N → ℝ) => runRetainedLiePointList D Φ fs w.1 w.2) = L ∘ F := by
    funext w
    exact congrArg Prod.snd (chronological_retainedLieAbsoluteStateMap D Φ fs w.1 w.2).symm
  rw [he,L.iteratedFDeriv_comp_left hF (by exact_mod_cast hjQ)]
  apply (L.norm_compContinuousMultilinearMap_le _).trans
  apply le_trans (mul_le_of_le_one_left (norm_nonneg _)
    (ContinuousLinearMap.norm_snd_le ℝ ℝ (Fin N → ℝ)))
  simpa only [List.length_map] using
    norm_chronologicalComposition_jet_le Q hB _ q h j hj hjQ
end RothschildStein.G3

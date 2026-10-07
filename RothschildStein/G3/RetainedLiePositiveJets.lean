-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.VariableStateEndpointJets
public import RothschildStein.G3.ParameterStatePositiveJets
public import RothschildStein.G3.RetainedLieStateMaps
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

def retainedLieAbsoluteStateMap {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (f : formalSpan a s p) (q : ℝ × (Fin N → ℝ)) : ℝ × (Fin N → ℝ) :=
  (q.1,finiteLieTimeOneMap Φ (dilatedInputCoordinates D f q.1,q.2))

/-- Actual retained updates inherit positive-jet bounds uniformly in position. -/
theorem norm_retainedLieAbsoluteStateMap_jet_le {a s N n : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (f : formalSpan a s p) (q : ℝ × (Fin N → ℝ)) (hn : 1 ≤ n)
    (hH : ContDiffAt ℝ n (finiteLieTimeOneMap Φ) (dilatedInputCoordinates D f q.1,q.2))
    {C A : ℝ} (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hHjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j (finiteLieTimeOneMap Φ)
      (dilatedInputCoordinates D f q.1,q.2)‖ ≤ C)
    (hfjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j
      (dilatedInputCoordinates D f) q.1‖ ≤ A) :
    ‖iteratedFDeriv ℝ n (retainedLieAbsoluteStateMap D Φ f) q‖ ≤
      max 1 ((n.factorial : ℝ)*C*A^n) := by
  let g := fun w : ℝ × (Fin N → ℝ) =>
    finiteLieTimeOneMap Φ (dilatedInputCoordinates D f w.1,w.2)
  have hi : ContDiffAt ℝ n (fun w : ℝ × (Fin N → ℝ) =>
      (dilatedInputCoordinates D f w.1,w.2)) q :=
    ((((dilatedInputCoordinates_contDiff D f).comp contDiff_fst).prodMk
      contDiff_snd).contDiffAt).of_le (by simp)
  have hg : ContDiffAt ℝ n g q := hH.comp (g := finiteLieTimeOneMap Φ)
    (f := fun w : ℝ × (Fin N → ℝ) => (dilatedInputCoordinates D f w.1,w.2)) q hi
  have hj := norm_variable_state_endpoint_jet_le (dilatedInputCoordinates D f)
    (dilatedInputCoordinates_contDiff D f) (finiteLieTimeOneMap Φ) q hn hH hC hA hHjet hfjet
  have he : parameterStateLift (0 : Fin N → ℝ) g = retainedLieAbsoluteStateMap D Φ f := by
    funext w
    simp only [parameterStateLift,retainedLieAbsoluteStateMap,g,sub_zero]
  rw [← he]
  exact norm_parameterStateLift_positive_jet_le 0 g q hn hg (le_max_left _ _)
    (hj.trans (le_max_right _ _))
end RothschildStein.G3

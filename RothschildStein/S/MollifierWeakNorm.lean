-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev
public import RothschildStein.S.WeakSub
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.MollifierAllDimensions
public import RothschildStein.S.MollifierZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function TopologicalSpace
open scoped Topology ContDiff ENNReal
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞}

/-- The weak-word norm of the mollifier error equals
the Lp error between the classical mollified word and its weak
representative (BB Thm 2.9, p. 73; norm identification). -/
theorem weakWordENorm_mollifier_error_eq
    (Ω U : Opens (Fin n → ℝ)) (hUΩ : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (hp : 1 ≤ p) {f g : (Fin n → ℝ) → ℝ} (hf : MemLp f p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (I : List (Fin q)) (hg : hasWeakWordDeriv X Ω I f g) {ε : ℝ} (hε : 0 < ε) :
    weakWordENorm X U I p
      (fun x => f x-euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε x) =
      eLpNorm (fun x => wordDerivative X I
        (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε) x-g x)
        p (volume.restrict (U : Set (Fin n → ℝ))) := by
  have hXu : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (U : Set (Fin n → ℝ)) :=
    fun j => (hX j).mono hUΩ
  have hm := contDiff_euclideanRegularize_all_dimensions
    (((memLp_zeroExtension_iff Ω.isOpen.measurableSet f).mpr hf).locallyIntegrable hp) hε
  have hc := hasWeakWordDeriv_classical U X hXu I
    (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε) hm.contDiffOn
  have hw := hasWeakWordDeriv_sub X U hXu (hasWeakWordDeriv_restrict X Ω U hUΩ hg) hc
  rw [weakWordENorm_eq X U I p _ _ hw]
  exact eLpNorm_sub_comm g (wordDerivative X I
    (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε)) p _

end RothschildStein.S

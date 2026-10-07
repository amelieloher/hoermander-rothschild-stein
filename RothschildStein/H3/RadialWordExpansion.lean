-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialTermDerivative
public import RothschildStein.H3.FieldListSums

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Filter
open scoped Topology

private theorem radial_sum_flatMap {α : Type*} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

/-- The finite radial chain-rule expansion for every ordered
 field word. The terms retain multiplicities and do not commute fields. -/
theorem wordDerivative_radial_expansion {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {ν : (Fin n → ℝ) → ℝ}
    (hν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (I : List (Fin m))
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    wordDerivative X I (F ∘ ν) x =
      ((radialWordTerms I).map (fun t => radialTermValue X ν F t x)).sum := by
  induction I generalizing x with
  | nil => simp [wordDerivative,radialWordTerms,radialTermValue,radialGaugeProduct,
      iteratedDeriv_zero]
  | cons i I ih =>
    have he : wordDerivative X I (F ∘ ν) =ᶠ[𝓝 x]
        (fun y => ((radialWordTerms I).map (fun t => radialTermValue X ν F t y)).sum) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
      exact ih hy
    have ha := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (X i x)) (he.fderiv_eq (𝕜 := ℝ))
    change fieldDerivative (X i) (wordDerivative X I (F ∘ ν)) x = _
    change fieldDerivative (X i) (wordDerivative X I (F ∘ ν)) x =
      fieldDerivative (X i)
        (fun y => ((radialWordTerms I).map (fun t => radialTermValue X ν F t y)).sum) x at ha
    rw [ha,fieldDerivative_list_sum (radialWordTerms I) (radialTermValue X ν F) (X i) x
      (fun t _ => radialTermValue_differentiableAt X hX hν hF t hx)]
    simp only [radialWordTerms,List.map_flatMap,radial_sum_flatMap,List.map_cons,
      List.sum_cons,List.map_map,Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t _
    exact fieldDerivative_radialTermValue X hX hν hF i t hx

end RothschildStein.H3

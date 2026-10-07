-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Transposes

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The raw scalar transpose preserves local smoothness
(BB (2.2)–(2.3), p. 68). -/
theorem contDiffOn_fieldTranspose (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fieldTranspose V f) (Ω : Set (Fin n → ℝ)) := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (fun y => f y • V y) x) (Ω : Set (Fin n → ℝ)) :=
    (hf.smul hV).fderiv_of_isOpen Ω.isOpen (by simp)
  unfold fieldTranspose Hormander.Interface.euclideanDivergence
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro i _
  exact (contDiff_apply ℝ ℝ i).comp_contDiffOn (hd.clm_apply contDiffOn_const)

end RothschildStein.S

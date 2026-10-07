-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FiniteJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A joint finite-dimensional value map has the same jet budget
as its components, using the supremum norm. -/
theorem HasJetBound.pi {E F ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : E → ι → F} (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f x i) Ω)
    {h : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hjets : ∀ i, HasJetBound Ω K (fun x => f x i) h P) :
    HasJetBound Ω K f h P := by
  have hfs : ContDiffOn ℝ (⊤ : ℕ∞) f Ω := contDiffOn_pi.mpr hf
  intro j hj x hx
  apply ContinuousMultilinearMap.opNorm_le_bound hP
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hP (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro i
  let L : (ι → F) →L[ℝ] F := ContinuousLinearMap.proj i
  have he := L.iteratedFDerivWithin_comp_left (hfs x (hKΩ hx)) hΩ.uniqueDiffOn
    (hKΩ hx) (i := j) (by simp)
  have hev := congrArg (fun A => A v) he
  have hb := ContinuousMultilinearMap.le_of_opNorm_le (hjets i j hj x hx) v
  change ‖L ((iteratedFDerivWithin ℝ j f Ω x) v)‖ ≤ P * ∏ k, ‖v k‖
  change (iteratedFDerivWithin ℝ j (fun x => f x i) Ω x) v =
    L ((iteratedFDerivWithin ℝ j f Ω x) v) at hev
  rw [← hev]
  exact hb

end RothschildStein.G4

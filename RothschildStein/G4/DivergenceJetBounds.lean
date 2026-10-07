-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LinearJetBounds
public import RothschildStein.G4.DeterminantMultiplier

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Finite sums add the scalar coefficient jet budgets. -/
theorem HasJetBound.sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (S : Finset ι) (f : ι → E → ℝ) (P : ι → ℝ) {h : ℕ}
    (hf : ∀ i ∈ S, ContDiffOn ℝ (⊤ : ℕ∞) (f i) Ω)
    (hb : ∀ i ∈ S, HasJetBound Ω K (f i) h (P i)) :
    HasJetBound Ω K (fun x => ∑ i ∈ S, f i x) h (∑ i ∈ S, P i) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_fun_sum_apply hΩ.uniqueDiffOn (hKΩ hx)
    (fun i hi => (hf i hi).of_le (by simp) x (hKΩ hx))]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hb i hi j hj x hx))

/-- The trace budget depends only on the finite coordinate space. -/
def divergenceJetMultiplier (n : ℕ) : ℝ :=
  ∑ i : Fin n, ‖(ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)‖ *
    ‖Hormander.Interface.basisVec i‖

/-- The trace budget is nonnegative. -/
theorem divergenceJetMultiplier_nonneg (n : ℕ) : 0 ≤ divergenceJetMultiplier n :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Divergence consumes exactly one input coefficient jet. -/
theorem HasJetBound.divergence {n h : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {Z : (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {P : ℝ}
    (hb : HasJetBound Ω K Z (h + 1) P) :
    HasJetBound Ω K (Hormander.Interface.euclideanDivergence Z) h
      (divergenceJetMultiplier n * P) := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (_root_.fderiv ℝ Z) Ω :=
    hZ.fderiv_of_isOpen hΩ (by simp)
  have hj := hb.fderiv hΩ hKΩ
  have hs : ∀ i : Fin n, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => _root_.fderiv ℝ Z x (Hormander.Interface.basisVec i)) Ω :=
    fun i => hd.clm_apply contDiffOn_const
  have ht : ∀ i : Fin n, HasJetBound Ω K
      (fun x => (_root_.fderiv ℝ Z x (Hormander.Interface.basisVec i)) i) h
      (‖(ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)‖ *
        ‖Hormander.Interface.basisVec i‖ * P) := by
    intro i
    have he := (hj.clm_apply_const hΩ hKΩ hd (Hormander.Interface.basisVec i)).linear_comp
      hΩ hKΩ (hs i) (ContinuousLinearMap.proj i)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, mul_assoc] using he
  have he := HasJetBound.sum hΩ hKΩ Finset.univ
    (fun i x => (_root_.fderiv ℝ Z x (Hormander.Interface.basisVec i)) i)
    (fun i => ‖(ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)‖ *
      ‖Hormander.Interface.basisVec i‖ * P)
    (fun i _ => contDiffOn_pi.mp (hs i) i) (fun i _ => ht i)
  change HasJetBound Ω K (fun x => ∑ i : Fin n, (_root_.fderiv ℝ Z x (Hormander.Interface.basisVec i)) i) h _
  simpa only [divergenceJetMultiplier,
    Finset.sum_mul] using he

end RothschildStein.G4

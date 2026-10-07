-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.DivergenceJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Finite vector sums add their input jet budgets. -/
theorem HasJetBound.finite_sum {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (S : Finset ι) (f : ι → E → F) (P : ι → ℝ) {h : ℕ}
    (hf : ∀ i ∈ S, ContDiffOn ℝ (⊤ : ℕ∞) (f i) Ω)
    (hb : ∀ i ∈ S, HasJetBound Ω K (f i) h (P i)) :
    HasJetBound Ω K (fun x => ∑ i ∈ S, f i x) h (∑ i ∈ S, P i) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_fun_sum_apply hΩ.uniqueDiffOn (hKΩ hx)
    (fun i hi => (hf i hi).of_le (by simp) x (hKΩ hx))]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hb i hi j hj x hx))

/-- A fixed control coefficient contributes its absolute value
at every vector-field jet order. -/
theorem HasJetBound.const_smul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : E → F} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {h : ℕ} {P : ℝ} (hfP : HasJetBound Ω K f h P) (a : ℝ) :
    HasJetBound Ω K (fun x => a • f x) h (|a| * P) := by
  intro j hj x hx
  change ‖iteratedFDerivWithin ℝ j (a • f) Ω x‖ ≤ |a| * P
  rw [iteratedFDerivWithin_const_smul_apply (hf.of_le (by simp) x (hKΩ hx))
    hΩ.uniqueDiffOn (hKΩ hx), norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hfP j hj x hx) (abs_nonneg a)

/-- The small constant-control vector field has a jet budget
linear in the sum of the control coefficients' absolute values. -/
theorem constantControlField_jet_bound {ι : Type*} [Fintype ι] {n h : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω) {P : ℝ}
    (hjets : ∀ i, HasJetBound Ω K (Z i) h P) (a : ι → ℝ) :
    HasJetBound Ω K (fun x => ∑ i, a i • Z i x) h ((∑ i, |a i|) * P) := by
  have hb := HasJetBound.finite_sum hΩ hKΩ Finset.univ (fun i x => a i • Z i x)
    (fun i => |a i| * P) (fun i _ => (contDiffOn_const (c := a i)).smul (hZ i))
    (fun i _ => (hjets i).const_smul hΩ hKΩ (hZ i) (a i))
  simpa only [Finset.sum_mul] using hb

end RothschildStein.G4

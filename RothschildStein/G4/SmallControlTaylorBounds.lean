-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FlowTaylorRemainder

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Positive weights give a linear coefficient-mass bound for
small weighted controls, uniformly over the fixed finite carrier. -/
theorem controlCoefficientMass_le {ι : Type*} [Fintype ι] (w : ι → ℕ+) (a : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (ha : ∀ i, |a i| ≤ δ ^ (w i : ℕ)) :
    (∑ i, |a i|) ≤ (Fintype.card ι : ℝ) * δ := by
  calc
    _ ≤ ∑ _ : ι, δ := Finset.sum_le_sum (fun i _ => (ha i).trans
      (pow_le_of_le_one hδ hδ1 (w i).ne_zero))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The actual weighted-control Taylor remainder has a uniform
constant times δ to the Taylor remainder order. This is the absolute
remainder used at orders ns−1 and 2ns−1 in BB pp. 434–436. -/
theorem small_control_flow_taylor_remainder_bound {ι : Type*} [Fintype ι] {n : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (w : ι → ℕ+) (a : ι → ℝ) {γ : ℝ → (Fin n → ℝ)}
    (hγs : ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 1))
    (hmap : MapsTo γ (Icc 0 1) K)
    (hγ : ∀ t ∈ Icc 0 1, HasDerivAt γ (∑ i, a i • Z i (γ t)) t)
    (m : ℕ) {P C δ : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hZP : ∀ i, HasJetBound Ω K (Z i) (m + 1) P)
    (hfC : HasJetBound Ω K f (m + 1) C)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (ha : ∀ i, |a i| ≤ δ ^ (w i : ℕ)) :
    |f (γ 1) - taylorWithinEval (f ∘ γ) m (Icc 0 1) 0 1| ≤
      (fieldIterationBudget 0 (m + 1) * C * ((Fintype.card ι : ℝ) * P) ^ (m + 1) /
        (m.factorial : ℝ)) * δ ^ (m + 1) := by
  have hm := controlCoefficientMass_le w a hδ hδ1 ha
  have hn : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hp : (∑ i, |a i|) * P ≤ ((Fintype.card ι : ℝ) * P) * δ := by
    have he := mul_le_mul_of_nonneg_right hm hP
    nlinarith
  have he := constant_control_flow_taylor_remainder_bound hΩ hKΩ hZ hf a hγs hmap hγ m
    hP hC hZP hfC
  apply he.trans
  calc
    _ ≤ fieldIterationBudget 0 (m + 1) * C *
        (((Fintype.card ι : ℝ) * P) * δ) ^ (m + 1) / (m.factorial : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hn hP) hp _)
        (mul_nonneg (fieldIterationBudget_nonneg _ _) hC)) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow]; ring

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FlowIterationJetBounds
public import RothschildStein.G4.VectorSumJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- An actual flow's Taylor remainder has the universal input-jet
budget times the corresponding power of its vector-field budget. -/
theorem flow_taylor_remainder_bound {n : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {T : (Fin n → ℝ) → (Fin n → ℝ)}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) T Ω) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) {γ : ℝ → (Fin n → ℝ)}
    (hγs : ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 1))
    (hmap : MapsTo γ (Icc 0 1) K)
    (hγ : ∀ t ∈ Icc 0 1, HasDerivAt γ (T (γ t)) t)
    (m : ℕ) {P C : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hTP : HasJetBound Ω K T (m + 1) P) (hfC : HasJetBound Ω K f (m + 1) C) :
    |f (γ 1) - taylorWithinEval (f ∘ γ) m (Icc 0 1) 0 1| ≤
      fieldIterationBudget 0 (m + 1) * C * P ^ (m + 1) / (m.factorial : ℝ) := by
  have hmapΩ : MapsTo γ (Icc 0 1) Ω := fun _ ht => hKΩ (hmap ht)
  have hi := iteratedDerivWithin_comp_flow hΩ hT hf (by norm_num : (0 : ℝ) < 1)
    hmapΩ hγ (m + 1)
  have hb := fieldIterates_jet_bound hΩ hKΩ hT hf (m + 1) 0 hP hC
    (by simpa only [zero_add] using hTP) (by simpa only [zero_add] using hfC)
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (m + 1) (f ∘ γ) (Icc 0 1) t‖ ≤
        fieldIterationBudget 0 (m + 1) * C * P ^ (m + 1) := by
    intro t ht
    rw [hi ht]
    simpa using hb 0 (Nat.zero_le _) (γ t) (hmap ht)
  have hs : ContDiffOn ℝ (m + 1) (f ∘ γ) (Icc 0 1) :=
    (hf.comp hγs hmapΩ).of_le (by simp)
  have he := taylor_mean_remainder_bound (by norm_num : (0 : ℝ) ≤ 1) hs
    (by constructor <;> norm_num : (1 : ℝ) ∈ Icc 0 1) hbound
  simpa only [Function.comp_apply, Real.norm_eq_abs, sub_zero, one_pow, mul_one] using he

/-- Constant controls yield a Taylor remainder with exactly the
required power of their small coefficient mass. -/
theorem constant_control_flow_taylor_remainder_bound {ι : Type*} [Fintype ι] {n : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (a : ι → ℝ) {γ : ℝ → (Fin n → ℝ)}
    (hγs : ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 1))
    (hmap : MapsTo γ (Icc 0 1) K)
    (hγ : ∀ t ∈ Icc 0 1, HasDerivAt γ (∑ i, a i • Z i (γ t)) t)
    (m : ℕ) {P C : ℝ} (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hZP : ∀ i, HasJetBound Ω K (Z i) (m + 1) P)
    (hfC : HasJetBound Ω K f (m + 1) C) :
    |f (γ 1) - taylorWithinEval (f ∘ γ) m (Icc 0 1) 0 1| ≤
      fieldIterationBudget 0 (m + 1) * C * ((∑ i, |a i|) * P) ^ (m + 1) /
        (m.factorial : ℝ) := by
  have hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∑ i, a i • Z i x) Ω :=
    ContDiffOn.sum (fun i _ => (contDiffOn_const (c := a i)).smul (hZ i))
  exact flow_taylor_remainder_bound hΩ hKΩ hT hf hγs hmap hγ m
    (mul_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hP) hC
    (constantControlField_jet_bound hΩ hKΩ hZ hZP a) hfC

end RothschildStein.G4

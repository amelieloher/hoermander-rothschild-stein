-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakHorizontalNorms
public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.H3.PhiBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- Restriction does not increase the finite horizontal weak norm. -/
theorem horizontalWeakENorm_mono_domain {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u) :
    horizontalWeakENorm X U p u ≤ horizontalWeakENorm X Ω p u := by
  apply Finset.sum_le_sum
  intro i _
  have hi : [i.succ] ∈ wordFamily driftWeight 2 := by
    simp [S.mem_wordFamily_iff, wordWeight, driftWeight, Fin.succ_ne_zero]
  obtain ⟨g,hg,_⟩ := hu.2 [i.succ] hi
  exact weakWordENorm_mono_domain X Ω U hU [i.succ] p u g hg

/-- Actual local Sobolev membership supplies finite Phi_1
for the fixed horizontal weak norms on quasiballs (BB p. 371). -/
theorem phi_horizontalWeak_lt_top {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G)
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (x₀ : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u) :
    phi (Ioo (1/2 : ℝ) 1) r 1
      (fun σ => (horizontalWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal) < ⊤ := by
  have hb : phi (Ioo (1/2 : ℝ) 1) r 1
      (fun σ => (horizontalWeakENorm X (quasiballDomain G ν x₀ (σ*r)) p u).toReal) ≤
      ENNReal.ofReal ((r/2)^1*(horizontalWeakENorm X (quasiballDomain G ν x₀ r) p u).toReal) := by
    apply phi_le_uniform_bound _ _ 1 hr ENNReal.toReal_nonneg
      (fun _ h => ⟨h.1.le,h.2⟩)
    intro σ hσ
    refine ⟨ENNReal.toReal_nonneg,?_⟩
    apply ENNReal.toReal_mono (horizontalWeakENorm_lt_top X _ p u hu).ne
    apply horizontalWeakENorm_mono_domain X _ _ _ p u hu
    intro x hx
    change G2.gaugeDistance G ν x x₀ < σ*r at hx
    change G2.gaugeDistance G ν x x₀ < r
    exact hx.trans_le (by nlinarith [hσ.2])
  exact hb.trans_lt ENNReal.ofReal_lt_top

end RothschildStein.H3

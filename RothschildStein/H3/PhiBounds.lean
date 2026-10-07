-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PhiAbsorption
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Metric
open scoped ENNReal

/-- The elementary upper bound in BB Definition 8.41, p. 371.
It applies to each derivative norm and their finite sums. -/
theorem phi_le_uniform_bound (I : Set ℝ) (N : ℝ → ℝ) {r B : ℝ} (k : ℕ)
    (hr : 0 < r) (_hB : 0 ≤ B) (hI : I ⊆ Ico (1 / 2 : ℝ) 1)
    (hN : ∀ σ ∈ I, 0 ≤ N σ ∧ N σ ≤ B) :
    phi I r k N ≤ ENNReal.ofReal ((r / 2) ^ k * B) := by
  apply iSup_le
  intro σ
  apply iSup_le
  intro hσ
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨hslo, hshi⟩ := hI hσ
  have hw : (1 - σ) ^ k * r ^ k ≤ (r / 2) ^ k := by
    rw [← mul_pow]
    gcongr
    nlinarith
  exact mul_le_mul hw (hN σ hσ).2 (hN σ hσ).1 (by positivity)

/-- A finite full-ball derivative norm makes the corresponding Phi
seminorm finite, giving the required finite first-order interpolation term. -/
theorem phi_lt_top_of_uniform_bound (I : Set ℝ) (N : ℝ → ℝ) {r B : ℝ} (k : ℕ)
    (hr : 0 < r) (hB : 0 ≤ B) (hI : I ⊆ Ico (1 / 2 : ℝ) 1)
    (hN : ∀ σ ∈ I, 0 ≤ N σ ∧ N σ ≤ B) : phi I r k N < ⊤ :=
  (phi_le_uniform_bound I N k hr hB hI hN).trans_lt ENNReal.ofReal_lt_top

/-- The half-radius lower bound for the open interval convention.
The endpoint follows by continuity of the weight; no continuity of N
is needed, only the lower bound supplied by nested-ball norm monotonicity. -/
theorem phi_half_radius_le {N : ℝ → ℝ} {r L : ℝ} (k : ℕ)
    (hr : 0 < r) (_hL : 0 ≤ L)
    (hN : ∀ σ ∈ Ioo (1 / 2 : ℝ) 1, L ≤ N σ) :
    ENNReal.ofReal ((r / 2) ^ k * L) ≤ phi (Ioo (1 / 2 : ℝ) 1) r k N := by
  by_cases htop : phi (Ioo (1 / 2 : ℝ) 1) r k N = ⊤
  · rw [htop]; exact le_top
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
  have hb (σ : ℝ) (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) :
      (1 - σ) ^ k * r ^ k * L ≤ (phi (Ioo (1 / 2 : ℝ) 1) r k N).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
    have hsup : ENNReal.ofReal ((1 - σ) ^ k * r ^ k * N σ) ≤
        phi (Ioo (1 / 2 : ℝ) 1) r k N :=
      le_iSup_of_le σ (le_iSup_of_le hσ le_rfl)
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hsup
    have hs : σ < 1 := hσ.2
    exact mul_le_mul_of_nonneg_left (hN σ hσ) (by positivity)
  have hclosure : (1 / 2 : ℝ) ∈ closure (Ioo (1 / 2 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    constructor <;> norm_num
  have he := le_on_closure hb (by fun_prop) continuousOn_const hclosure
  convert he using 1; ring

end RothschildStein.H3

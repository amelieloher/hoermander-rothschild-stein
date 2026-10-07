-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SpatialLiftJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G1

/-- Adjoining a time-speed parameter costs only an explicit
finite coefficient-jet constant (BB Prop 1.2, pp. 3–4). -/
theorem norm_time_rescaled_field_jet_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {Z : E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {a ε B : ℝ} {x : E}
    (hx : x ∈ Ω) (ha : |a| ≤ 1) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (R : ℕ) (hjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j Z x‖ ≤ B)
    (n : ℕ) (hn : n ≤ R) :
    ‖iteratedFDeriv ℝ n (fun q : ℝ × E => (ε * q.1) • Z q.2) (a, x)‖ ≤
      ε * 2 ^ n * R.factorial * B := by
  let S : Set (ℝ × E) := univ ×ˢ Ω
  have hS : IsOpen S := isOpen_univ.prod hΩ
  have hp : (a, x) ∈ S := ⟨mem_univ _, hx⟩
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E => ε * q.1) :=
    contDiff_const.mul contDiff_fst
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × E => Z q.2) S :=
    hZ.comp contDiffOn_snd (fun q hq => hq.2)
  have hcoeff : ∀ j, ‖iteratedFDeriv ℝ j (fun q : ℝ × E => ε * q.1) (a, x)‖ ≤ ε := by
    intro j
    let L : (ℝ × E) →L[ℝ] ℝ := ε • ContinuousLinearMap.fst ℝ ℝ E
    have hL : ‖L‖ ≤ ε := by
      apply ContinuousLinearMap.opNorm_le_bound L hε
      intro q
      change ‖ε * q.1‖ ≤ ε * ‖q‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hε]
      exact mul_le_mul_of_nonneg_left (norm_fst_le q) hε
    have hv : ‖(0 : ℝ) + L (a, x)‖ ≤ ε := by
      change ‖0 + ε * a‖ ≤ ε
      simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg hε] using
        mul_le_mul_of_nonneg_left ha hε
    have hh := RothschildStein.G4.norm_affine_jet_le L 0 (a, x) j hv hL
    change ‖iteratedFDeriv ℝ j (fun q : ℝ × E => 0 + ε * q.1) (a, x)‖ ≤ ε at hh
    simpa only [zero_add] using hh
  have hh := norm_iteratedFDerivWithin_smul_le hc.contDiffOn hw hS.uniqueDiffOn hp
    (n := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hS hp] at hh
  apply hh.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * ε * (R.factorial * B) := by
      apply Finset.sum_le_sum
      intro j hj
      have hnr : n - j ≤ R := (Nat.sub_le n j).trans hn
      have hv := RothschildStein.G4.norm_spatial_lift_jet_le hΩ Z hZ a hx
        (n - j) (fun l hl => hjet l (hl.trans hnr))
      have hv' : ‖iteratedFDeriv ℝ (n - j) (fun q : ℝ × E => Z q.2) (a, x)‖ ≤
          R.factorial * B := hv.trans (mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.factorial_le hnr) hB)
      gcongr
      exact hcoeff j
    _ = _ := by
      simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

end RothschildStein.G1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Gauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- A continuous homogeneous gauge satisfies a global product bound
(BB Prop 3.9, p. 100). -/
theorem gauge_mul_bound {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x y, ν (G.mul x y) ≤ C * (ν x + ν y) := by
  have hc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => ν (G.mul p.1 p.2)) := by
    apply hν.1.comp
    apply continuous_pi
    intro j
    exact (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
      (continuous_pi fun i => Sum.casesOn i
        (fun k => (continuous_apply k).comp continuous_fst)
        (fun k => (continuous_apply k).comp continuous_snd))
  obtain ⟨C, hC⟩ := ((isCompact_gauge_le hν 1).prod (isCompact_gauge_le hν 1)).bddAbove_image
    hc.continuousOn
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro x y
  have hl : 0 ≤ ν x + ν y := add_nonneg (hν.2.1 x) (hν.2.1 y)
  by_cases hz : ν x + ν y = 0
  · have hx : x = 0 := (hν.2.2.1 x).mp ((add_eq_zero_iff_of_nonneg
      (hν.2.1 x) (hν.2.1 y)).mp hz).1
    have hy : y = 0 := (hν.2.2.1 y).mp ((add_eq_zero_iff_of_nonneg
      (hν.2.1 x) (hν.2.1 y)).mp hz).2
    subst x; subst y
    change ν (polynomialProduct G.productPolynomial 0 0) ≤ _
    rw [G.zero_left, (hν.2.2.1 0).mpr rfl]
    simp
  · have hp : 0 < ν x + ν y := lt_of_le_of_ne hl (Ne.symm hz)
    let t := (ν x + ν y)⁻¹
    have ht : 0 < t := inv_pos.mpr hp
    have hnx : ν (G.dilate t x) ≤ 1 := by
      rw [hν.2.2.2 t ht]
      dsimp [t]
      exact (inv_mul_le_iff₀ hp).mpr (by linarith [hν.2.1 y])
    have hny : ν (G.dilate t y) ≤ 1 := by
      rw [hν.2.2.2 t ht]
      dsimp [t]
      exact (inv_mul_le_iff₀ hp).mpr (by linarith [hν.2.1 x])
    have hb : ν (G.mul (G.dilate t x) (G.dilate t y)) ≤ C :=
      hC ⟨(G.dilate t x, G.dilate t y), ⟨hnx, hny⟩, rfl⟩
    have hd : G.dilate t (G.mul x y) = G.mul (G.dilate t x) (G.dilate t y) :=
      G.dilation_product t ht x y
    rw [← hd, hν.2.2.2 t ht] at hb
    have hb' : ν (G.mul x y) ≤ C * (ν x + ν y) := by
      dsimp [t] at hb
      simpa [mul_comm] using (inv_mul_le_iff₀ hp).mp hb
    exact hb'.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) hl)

/-- A gauge satisfying the product and inversion identities obeys the inverse bound (BB Proposition 3.9, p. 100; see also Proposition 3.7, p. 98). -/
theorem gauge_inv_bound_of_groupIdentities
    (hinv : ∀ t : ℝ, 0 < t → ∀ x, G.inv (G.dilate t x) = G.dilate t (G.inv x))
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, ν (G.inv x) ≤ C * ν x := by
  have hc : Continuous (fun x => ν (G.inv x)) := hν.1.comp
    (continuous_pi fun j => MvPolynomial.continuous_eval (p := G.inversePolynomial j))
  obtain ⟨C, hC⟩ := (isCompact_gauge_le hν 1).bddAbove_image hc.continuousOn
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    have hi : G.inv 0 = 0 := by
      calc
        G.inv 0 = G.mul (G.inv 0) 0 := (G.zero_right _).symm
        _ = 0 := G.inverse_left 0
    rw [hi, (hν.2.2.1 0).mpr rfl]
    simp
  · have hp := gauge_pos hν hx
    have hn := gauge_normalize hν hx
    have hb : ν (G.inv (G.dilate (ν x)⁻¹ x)) ≤ C :=
      hC ⟨G.dilate (ν x)⁻¹ x, hn.le, rfl⟩
    rw [hinv _ (inv_pos.mpr hp), hν.2.2.2 _ (inv_pos.mpr hp)] at hb
    have hb' : ν (G.inv x) ≤ C * ν x := by
      simpa [mul_comm] using (inv_mul_le_iff₀ hp).mp hb
    exact hb'.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) hp.le)

/-- The exact inversion and dilation identities give one constant for inversion and products (BB Proposition 3.9, pp. 99–100). -/
theorem gauge_norm_bounds_of_groupIdentities
    (hinv : ∀ t : ℝ, 0 < t → ∀ x, G.inv (G.dilate t x) = G.dilate t (G.inv x))
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ x, ν (G.inv x) ≤ C * ν x) ∧
      ∀ x y, ν (G.mul x y) ≤ C * (ν x + ν y) := by
  obtain ⟨Ci, hi, hbi⟩ := gauge_inv_bound_of_groupIdentities hinv hν
  obtain ⟨Cm, hm, hbm⟩ := gauge_mul_bound hν
  refine ⟨max Ci Cm, hi.trans (le_max_left _ _), ?_, ?_⟩
  · intro x
    exact (hbi x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hν.2.1 x))
  · intro x y
    exact (hbm x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg (hν.2.1 x) (hν.2.1 y)))

end RothschildStein.G2

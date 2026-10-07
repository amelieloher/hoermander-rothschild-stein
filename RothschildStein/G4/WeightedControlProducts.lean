-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ControlWordExpansion

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Weighted coefficient products cancel the precise derivative
radius losses and leave one smallness factor per derivative. -/
theorem weightedControlProduct_le {ι : Type*} (w : ι → ℕ+) (a : ι → ℝ)
    {e r : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) (hr : 0 < r)
    (ha : ∀ i, |a i| ≤ (e * r) ^ (w i : ℕ)) (L : List ι) :
    (L.map (fun i => |a i|)).prod * r ^ (-derivativeWeight w L) ≤ e ^ L.length := by
  have hsingle : ∀ i, |a i| * r ^ (-((w i : ℕ) : ℤ)) ≤ e := by
    intro i
    calc
      _ ≤ (e * r) ^ (w i : ℕ) * r ^ (-((w i : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_right (ha i) (zpow_nonneg hr.le _)
      _ = e ^ (w i : ℕ) := by
        rw [mul_pow, zpow_neg, zpow_natCast]
        field_simp
      _ ≤ e := pow_le_of_le_one he he1 (w i).ne_zero
  induction L with
  | nil => simp [derivativeWeight]
  | cons i L ih =>
    have hw : -derivativeWeight w (i :: L) = -((w i : ℕ) : ℤ) + -derivativeWeight w L := by
      simp only [derivativeWeight, List.map_cons, List.sum_cons, neg_add_rev]
      omega
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [hw, zpow_add₀ (ne_of_gt hr)]
    calc
      _ = (|a i| * r ^ (-((w i : ℕ) : ℤ))) *
          ((L.map (fun i => |a i|)).prod * r ^ (-derivativeWeight w L)) := by ring
      _ ≤ e * e ^ L.length := mul_le_mul (hsingle i) ih
        (mul_nonneg (List.prod_nonneg (fun _ hi => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
          exact abs_nonneg _)) (zpow_nonneg hr.le _)) he
      _ = _ := by rw [pow_succ]; ring

/-- The actual constant-control derivative power inherits the
weighted ordered-word bound at the initial point, with a numerical
finite-carrier count. -/
theorem fieldIterates_weighted_control_bound {ι : Type*} [Fintype ι] {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (w : ι → ℕ+) (a : ι → ℝ) (j : ℕ) {x : Fin n → ℝ} (hx : x ∈ Ω)
    {e r t C D : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) (hr : 0 < r) (ht : 0 < t)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : ∀ i, |a i| ≤ (e * r) ^ (w i : ℕ))
    (hwords : ∀ L : List ι, L.length = j → |shortDerivatives Z L f x| ≤
      C * t⁻¹ ^ j * r ^ (-derivativeWeight w L) * D) :
    |fieldIterates (fun y => ∑ i, a i • Z i y) j f x| ≤
      (Fintype.card ι : ℝ) ^ j * C * t⁻¹ ^ j * e ^ j * D := by
  classical
  rw [fieldIterates_constantControl_expansion hΩ hZ a hf j hx]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hterm : ∀ L : Fin j → ι,
      |(∏ i, a (L i)) * shortDerivatives Z (List.ofFn L) f x| ≤ C * t⁻¹ ^ j * e ^ j * D := by
    intro L
    have hb := hwords (List.ofFn L) List.length_ofFn
    have hp := weightedControlProduct_le w a he he1 hr ha (List.ofFn L)
    simp only [List.map_ofFn, List.prod_ofFn, List.length_ofFn] at hp
    rw [abs_mul, Finset.abs_prod]
    calc
      _ ≤ (∏ i, |a (L i)|) * (C * t⁻¹ ^ j * r ^ (-derivativeWeight w (List.ofFn L)) * D) :=
        mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
      _ = ((∏ i, |a (L i)|) * r ^ (-derivativeWeight w (List.ofFn L))) * (C * t⁻¹ ^ j * D) := by ring
      _ ≤ e ^ j * (C * t⁻¹ ^ j * D) := mul_le_mul_of_nonneg_right hp
        (mul_nonneg (mul_nonneg hC (pow_nonneg (inv_nonneg.mpr ht.le) _)) hD)
      _ = _ := by ring
  calc
    _ ≤ ∑ _ : Fin j → ι, C * t⁻¹ ^ j * e ^ j * D := Finset.sum_le_sum (fun L _ => hterm L)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]; ring

end RothschildStein.G4

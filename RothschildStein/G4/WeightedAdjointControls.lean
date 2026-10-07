-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AdjointFrameExpansion
public import RothschildStein.G4.WeightedControlProducts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Weighted ordered-bracket bounds pass to actual repeated
constant-control adjoints. Each coefficient cancels its radius loss and
leaves one smallness factor per bracket (BB pp. 443–444). -/
theorem adjoint_weighted_control_frameCoefficient_bound
    {ι σ : Type*} [Fintype ι] {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {W : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    {Y : (Fin n → ℝ) → (Fin n → ℝ)} (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    (Z : σ → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → σ)
    (w : ι → ℕ+) (a : ι → ℝ) (j : ℕ) (i : Fin n)
    {x : Fin n → ℝ} (hx : x ∈ Ω) {e r C : ℝ} {d : ℤ}
    (he : 0 ≤ e) (he1 : e ≤ 1) (hr : 0 < r) (hC : 0 ≤ C)
    (ha : ∀ k, |a k| ≤ (e * r) ^ (w k : ℕ))
    (hwords : ∀ L : List ι, L.length = j →
      |frameCoefficient Z B (orderedAdjoints W L Y) i x| ≤
        C * r ^ (d - derivativeWeight w L)) :
    |frameCoefficient Z B
      ((VectorField.lieBracket ℝ (fun y => ∑ k, a k • W k y))^[j] Y) i x| ≤
      (Fintype.card ι : ℝ) ^ j * C * e ^ j * r ^ d := by
  classical
  rw [adjoint_constantControl_frameCoefficient_expansion hΩ hW a hY Z B j i hx]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hterm : ∀ L : Fin j → ι,
      |(∏ k, a (L k)) * frameCoefficient Z B
        (orderedAdjoints W (List.ofFn L) Y) i x| ≤ C * e ^ j * r ^ d := by
    intro L
    have hb := hwords (List.ofFn L) List.length_ofFn
    have hp := weightedControlProduct_le w a he he1 hr ha (List.ofFn L)
    simp only [List.map_ofFn, List.prod_ofFn, List.length_ofFn] at hp
    rw [abs_mul, Finset.abs_prod]
    calc
      _ ≤ (∏ k, |a (L k)|) * (C * r ^ (d - derivativeWeight w (List.ofFn L))) :=
        mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
      _ = ((∏ k, |a (L k)|) * r ^ (-derivativeWeight w (List.ofFn L))) * (C * r ^ d) := by
        rw [sub_eq_add_neg, zpow_add₀ (ne_of_gt hr)]
        ring
      _ ≤ e ^ j * (C * r ^ d) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg hC (zpow_nonneg hr.le _))
      _ = _ := by ring
  calc
    _ ≤ ∑ _ : Fin j → ι, C * e ^ j * r ^ d := Finset.sum_le_sum (fun L _ => hterm L)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]; ring

end RothschildStein.G4

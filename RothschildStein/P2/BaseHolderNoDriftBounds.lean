-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderNoDriftProduct
public import RothschildStein.P2.BaseHolderNoDriftCompact

/-!
# No drift: sup and Hölder bounds for `L̃ (u ζ)`

For the cutoff estimate (`L̃(ζ u) = ζ L̃u + 2 ∑ᵢ X̃ᵢζ X̃ᵢu + u L̃ζ`), alphabet `Fin q`, all weights
one. For the Leibniz jet `prodJetNoDrift` of `u ζ`:

* `ofReal_abs_weakSumSquares_prod_le`: the pointwise bound of `|L̃ (u ζ)|` by the three summands;
* `supNormE_weakSumSquares_prod_le`: the sup bound `‖L̃ (u ζ)‖_∞ ≤ M_f + 2 β₁ Ψ + β₂ M_u` for a cutoff
  `0 ≤ ζ ≤ 1` with `|X̃ᵢ ζ| ≤ β₁`, `|L̃ ζ| ≤ β₂` supported in a set where `|L̃u| ≤ M_f`, `|u| ≤ M_u` and
  `∑ᵢ |X̃ᵢ u| ≤ Ψ`;
* `holderENorm_two_mul_sum_le`: the Hölder norm of `2 ∑ᵢ gᵢ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Pointwise

variable {q N : ℕ}

/-- The pointwise bound of `|L̃ (u ζ)|` by the three summands of the Leibniz rule. -/
theorem ofReal_abs_weakSumSquares_prod_le (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (ζ u : (Fin N → ℝ) → ℝ) (D : List (Fin q) → (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    ENNReal.ofReal |weakSumSquares (prodJetNoDrift X ζ u D) [] x| ≤
      ENNReal.ofReal |weakSumSquares D [] x| * ENNReal.ofReal |ζ x| +
        2 * ∑ i : Fin q, ENNReal.ofReal |D [i] x| * ENNReal.ofReal |fieldDerivative (X i) ζ x| +
          ENNReal.ofReal |u x| * ENNReal.ofReal |sumSquares X ζ x| := by
  rw [weakSumSquares_prodJetNoDrift]
  set a : ℝ := weakSumSquares D [] x * ζ x with ha
  set b : ℝ := 2 * ∑ i : Fin q, D [i] x * fieldDerivative (X i) ζ x with hb
  set c : ℝ := u x * sumSquares X ζ x with hc
  have h1 : |a + b + c| ≤ |a| + |b| + |c| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hb' : ENNReal.ofReal |b| ≤
      2 * ∑ i : Fin q, ENNReal.ofReal |D [i] x| * ENNReal.ofReal |fieldDerivative (X i) ζ x| := by
    have h2 : |b| ≤ 2 * ∑ i : Fin q, |D [i] x| * |fieldDerivative (X i) ζ x| := by
      rw [hb, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
    calc ENNReal.ofReal |b| ≤ ENNReal.ofReal (2 * ∑ i : Fin q, |D [i] x| *
          |fieldDerivative (X i) ζ x|) := ENNReal.ofReal_le_ofReal h2
      _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg
            (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))]
          simp only [ENNReal.ofReal_ofNat]
          congr 1
          exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul (abs_nonneg _)
  calc ENNReal.ofReal |a + b + c| ≤ ENNReal.ofReal (|a| + |b| + |c|) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal |a| + ENNReal.ofReal |b| + ENNReal.ofReal |c| := by
        rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ ≤ _ := by
        refine add_le_add (add_le_add ?_ hb') ?_
        · rw [ha, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
        · rw [hc, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]

/-- **The sup norm of `L̃ (u ζ)`**: for a cutoff `0 ≤ ζ ≤ 1` with `tsupport ζ ⊆ B`,
`|X̃ᵢ ζ| ≤ β₁`, `|L̃ ζ| ≤ β₂`, and `|L̃u| ≤ M_f`, `|u| ≤ M_u`, `∑ᵢ |X̃ᵢ u| ≤ Ψ` on `B`,
`‖L̃ (u ζ)‖_{∞, V} ≤ M_f + 2 β₁ Ψ + β₂ M_u`. -/
theorem supNormE_weakSumSquares_prod_le (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {ζ u : (Fin N → ℝ) → ℝ} {D : List (Fin q) → (Fin N → ℝ) → ℝ} {V B : Set (Fin N → ℝ)}
    (hζB : tsupport ζ ⊆ B) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) {β₁ β₂ : ℝ} (_hβ₁ : 0 ≤ β₁)
    (h1 : ∀ i x, |fieldDerivative (X i) ζ x| ≤ β₁) (h2 : ∀ x, |sumSquares X ζ x| ≤ β₂)
    {Mf Mu Ψ : ℝ≥0∞} (hf : ∀ x ∈ B, ENNReal.ofReal |weakSumSquares D [] x| ≤ Mf)
    (hu : ∀ x ∈ B, ENNReal.ofReal |u x| ≤ Mu)
    (hΨ : ∀ x ∈ B, ∑ i : Fin q, ENNReal.ofReal |D [i] x| ≤ Ψ) :
    supNormE V (weakSumSquares (prodJetNoDrift X ζ u D) []) ≤
      Mf + ENNReal.ofReal (2 * β₁) * Ψ + ENNReal.ofReal β₂ * Mu := by
  refine supNormE_le_of_forall fun x _ => ?_
  by_cases hx : x ∈ tsupport ζ
  · have hxB := hζB hx
    refine (ofReal_abs_weakSumSquares_prod_le X ζ u D x).trans ?_
    have hz1 : ENNReal.ofReal |ζ x| ≤ 1 := by
      rw [abs_of_nonneg (hζ0 x)]
      exact ENNReal.ofReal_le_one.2 (hζ1 x)
    have t1 : ENNReal.ofReal |weakSumSquares D [] x| * ENNReal.ofReal |ζ x| ≤ Mf :=
      (mul_le_mul' (hf x hxB) hz1).trans (by rw [mul_one])
    have t2 : 2 * ∑ i : Fin q, ENNReal.ofReal |D [i] x| * ENNReal.ofReal |fieldDerivative (X i) ζ x| ≤
        ENNReal.ofReal (2 * β₁) * Ψ := by
      have hs : ∑ i : Fin q, ENNReal.ofReal |D [i] x| * ENNReal.ofReal |fieldDerivative (X i) ζ x| ≤
          Ψ * ENNReal.ofReal β₁ := by
        calc _ ≤ ∑ i : Fin q, ENNReal.ofReal |D [i] x| * ENNReal.ofReal β₁ :=
              Finset.sum_le_sum fun i _ =>
                mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (h1 i x))
          _ = (∑ i : Fin q, ENNReal.ofReal |D [i] x|) * ENNReal.ofReal β₁ := by
              rw [Finset.sum_mul]
          _ ≤ _ := mul_le_mul' (hΨ x hxB) le_rfl
      calc _ ≤ 2 * (Ψ * ENNReal.ofReal β₁) := mul_le_mul' le_rfl hs
        _ = ENNReal.ofReal (2 * β₁) * Ψ := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
            ring
    have t3 : ENNReal.ofReal |u x| * ENNReal.ofReal |sumSquares X ζ x| ≤ ENNReal.ofReal β₂ * Mu := by
      calc _ ≤ Mu * ENNReal.ofReal β₂ := mul_le_mul' (hu x hxB) (ENNReal.ofReal_le_ofReal (h2 x))
        _ = _ := mul_comm _ _
    exact add_le_add (add_le_add t1 t2) t3
  · have h0 : ζ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h1' : ∀ i : Fin q, fieldDerivative (X i) ζ x = 0 := fun i =>
      fieldDerivative_eq_zero_of_notMem_tsupport hx
    have h2' : sumSquares X ζ x = 0 := by
      unfold sumSquares
      exact Finset.sum_eq_zero fun i _ => fieldDerivative_fieldDerivative_eq_zero_of_notMem_tsupport hx
    rw [weakSumSquares_prodJetNoDrift]
    simp only [h0, h1', h2', mul_zero, Finset.sum_const_zero, add_zero, abs_zero, ENNReal.ofReal_zero]
    exact zero_le

/-- The Hölder norm of `2 ∑ᵢ gᵢ` is at most `2 ∑ᵢ ‖gᵢ‖`. -/
theorem holderENorm_two_mul_sum_le {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α)
    {V : Set (Fin N → ℝ)} {ι : Type*} (s : Finset ι) (g : ι → (Fin N → ℝ) → ℝ) :
    holderENorm d α V (fun x => 2 * ∑ i ∈ s, g i x) ≤ 2 * ∑ i ∈ s, holderENorm d α V (g i) := by
  have e : (fun x => 2 * ∑ i ∈ s, g i x) = fun x => (∑ i ∈ s, g i x) + ∑ i ∈ s, g i x := by
    funext x
    ring
  rw [e, two_mul]
  exact (holderENorm_add_le hα _ _).trans
    (add_le_add (holderENorm_finset_sum_le hα s g) (holderENorm_finset_sum_le hα s g))

end Pointwise

end RothschildStein.P2

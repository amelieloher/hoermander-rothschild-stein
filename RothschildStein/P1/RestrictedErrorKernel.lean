-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorChart

/-!
# Restricted-error bounds: the kernel hypotheses

`RestrictedKernelBounds K₀ k A B` is the exact conclusion of the lifted kernel estimates
at `ℓ = 1` (`LiftedChart.exists_kernel_estimates_cutoff`, `exists_kernel_estimates`): the size bound
`|k(ξ, η)| ≤ A d̃(ξ, η)^(1-Q)` and the two-variable difference bound
`|k(ξ', η) - k(ξ, η)| + |k(η, ξ') - k(η, ξ)| ≤ B d̃(ξ, ξ') / d̃(ξ', η)^Q` for
`d̃(ξ', η) > 2 d̃(ξ, ξ')`, on a compact `K₀ ⊆ U`; they are only required for `d̃(ξ', η) < 2`
(all that matters for `r_* ≤ 1`). The kernel cut to `K₀ × K₀` off the diagonal is assumed measurable
(it is continuous off the diagonal for the kernels of the kernel estimates, `measurable_sliceKernel_of_continuousOn`,
`exists_restrictedKernelBounds_kernelValue`).

`of_estimates` converts the conclusion of the kernel estimates at `ℓ = 1` to this form, `add` sums two kernels, and
`of_regular` accommodates bounded regular terms (`|r| ≤ M`, Lipschitz for `d̃`) and `mul_cutoff`
bounded `d̃`-Lipschitz cutoffs `a(ξ) b(η)`, as the decomposition of `F_R^chart` needs;
`sliceBounds` gives the abstract `SliceBounds` on `U_r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- A kernel continuous on `K₀ × K₀` off the diagonal has measurable
slice: the cut kernel is measurable. -/
theorem measurable_sliceKernel_of_continuousOn {N : ℕ} {K₀ : Set (Fin N → ℝ)} {k : (Fin N → ℝ) →
    (Fin N → ℝ) → ℝ} (hK₀ : MeasurableSet K₀)
    (hk : ContinuousOn (Function.uncurry k) ((K₀ ×ˢ K₀) \ Set.diagonal (Fin N → ℝ))) :
    Measurable (Function.uncurry (sliceKernel K₀ k)) := by
  classical
  have hT : MeasurableSet ((K₀ ×ˢ K₀) \ Set.diagonal (Fin N → ℝ)) :=
    (hK₀.prod hK₀).diff isClosed_diagonal.measurableSet
  have : Function.uncurry (sliceKernel K₀ k) =
      ((K₀ ×ˢ K₀) \ Set.diagonal (Fin N → ℝ)).piecewise (Function.uncurry k) 0 := by
    funext z
    simp only [Function.uncurry, sliceKernel, Set.piecewise_eq_indicator]
    rfl
  rw [this]
  exact ContinuousOn.measurable_piecewise hk continuousOn_const hT

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- **The kernel hypotheses of the restricted-error bounds**: the conclusion of the
lifted kernel estimates at `ℓ = 1` on the compact `K₀ ⊆ U`, for `d̃ < 2`, plus measurability of
the cut kernel. `size`: `|k(ξ, η)| ≤ A d̃(ξ, η)^(1-Q)` (`ξ ≠ η`); `diff`: for
`d̃(ξ', η) > 2 d̃(ξ, ξ')`,
`|k(ξ', η) - k(ξ, η)| + |k(η, ξ') - k(η, ξ)| ≤ B d̃(ξ, ξ') / d̃(ξ', η)^Q`. -/
structure RestrictedKernelBounds (K₀ : Set (Fin (n + m) → ℝ))
    (kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) (A B : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  measurable : Measurable (Function.uncurry (sliceKernel K₀ kk))
  size : ∀ ξ ∈ K₀, ∀ η ∈ K₀, ξ ≠ η → C.dl ξ η < 2 →
    |kk ξ η| ≤ A * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ))
  diff : ∀ ξ ∈ K₀, ∀ ξ' ∈ K₀, ∀ η ∈ K₀, 2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
    C.dl ξ' η < 2 →
    |kk ξ' η - kk ξ η| + |kk η ξ' - kk η ξ| ≤
      B * (C.dl ξ ξ').toReal / (C.dl ξ' η).toReal ^ C.G.homogeneousDimension

variable {C}

/-- **The kernel estimates discharge the hypotheses**: the conclusion of
`LiftedChart.exists_kernel_estimates_cutoff` (and `exists_kernel_estimates`) at `ℓ = 1`, for a kernel
`kk` with measurable cut, gives `RestrictedKernelBounds`. -/
theorem RestrictedKernelBounds.of_estimates {K₀ : Set (Fin (n + m) → ℝ)}
    {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmeas : Measurable (Function.uncurry (sliceKernel K₀ kk)))
    (hsize : ∀ ξ ∈ K₀, ∀ η ∈ K₀, ξ ≠ η →
      |kk ξ η| ≤ A * (C.dl ξ η).toReal ^ (((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ)))
    (hdiff : ∀ ξ ∈ K₀, ∀ ξ' ∈ K₀, ∀ η ∈ K₀, 2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
      |kk ξ' η - kk ξ η| + |kk η ξ' - kk η ξ| ≤
        B * (C.dl ξ ξ').toReal /
          (C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - ((1 : ℕ) : ℤ))) :
    C.RestrictedKernelBounds K₀ kk A B := by
  refine ⟨hA, hB, hmeas, fun ξ hξ η hη hne _ => ?_, fun ξ hξ ξ' hξ' η hη hsep _ => ?_⟩
  · simpa only [Nat.cast_one] using hsize ξ hξ η hη hne
  · have := hdiff ξ hξ ξ' hξ' η hη hsep
    rwa [Nat.cast_one, add_sub_cancel_right, zpow_natCast] at this

/-- **The abstract hypotheses on `U_r`**: the cut kernel
`sliceKernel S kk` of a kernel with `RestrictedKernelBounds` satisfies the abstract `SliceBounds`
for the real distance `d̃.toReal` on any measurable `S ⊆ K₀ ∩ O` of `d̃`-diameter `< 2`, with
`q + 1 = Q`. -/
theorem RestrictedKernelBounds.sliceBounds {K₀ : Set (Fin (n + m) → ℝ)}
    {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {A B : ℝ}
    (hk : C.RestrictedKernelBounds K₀ kk A B) {S : Set (Fin (n + m) → ℝ)} (hSK : S ⊆ K₀)
    (hSm : MeasurableSet S) (hSO : S ⊆ C.O) (hd2 : ∀ x ∈ S, ∀ y ∈ S, C.dl x y < 2) :
    SliceBounds S (fun x y => (C.dl x y).toReal) (C.G.homogeneousDimension - 1)
      (sliceKernel S kk) A B := by
  have hQ : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  refine ⟨hk.A_nonneg, hk.B_nonneg, ?_, fun x y hx => sliceKernel_of_not_mem (Or.inl hx),
    fun x y hy => sliceKernel_of_not_mem (Or.inr (Or.inl hy)), ?_, ?_⟩
  · have : Function.uncurry (sliceKernel S kk) =
        (S ×ˢ S).indicator (Function.uncurry (sliceKernel K₀ kk)) := by
      funext ⟨a, b⟩
      show sliceKernel S kk a b = (S ×ˢ S).indicator (Function.uncurry (sliceKernel K₀ kk)) (a, b)
      by_cases hab : a ∈ S ∧ b ∈ S
      · rw [Set.indicator_of_mem (show (a, b) ∈ S ×ˢ S from hab)]
        by_cases heq : a = b
        · rw [sliceKernel_of_not_mem (Or.inr (Or.inr heq)), Function.uncurry_apply_pair,
            sliceKernel_of_not_mem (Or.inr (Or.inr heq))]
        · rw [sliceKernel_of_mem hab.1 hab.2 heq, Function.uncurry_apply_pair,
            sliceKernel_of_mem (hSK hab.1) (hSK hab.2) heq]
      · rw [Set.indicator_of_notMem (show (a, b) ∉ S ×ˢ S from hab)]
        refine sliceKernel_of_not_mem ?_
        by_contra hcon
        exact hab ⟨by_contra fun h => hcon (Or.inl h), by_contra fun h => hcon (Or.inr (Or.inl h))⟩
    rw [this]
    exact hk.measurable.indicator (hSm.prod hSm)
  · intro x hx y hy
    show |sliceKernel S kk x y| ≤ A / (C.dl x y).toReal ^ (C.G.homogeneousDimension - 1)
    by_cases hxy : x = y
    · rw [sliceKernel_of_not_mem (Or.inr (Or.inr hxy))]
      simp only [abs_zero]
      exact div_nonneg hk.A_nonneg (pow_nonneg ENNReal.toReal_nonneg _)
    · rw [sliceKernel_of_mem hx hy hxy]
      have := hk.size x (hSK hx) y (hSK hy) hxy (hd2 x hx y hy)
      have e : (1 : ℤ) - (C.G.homogeneousDimension : ℤ) =
          -((C.G.homogeneousDimension - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hQ]
        push_cast
        ring
      rwa [e, zpow_neg, zpow_natCast, ← div_eq_mul_inv] at this
  · intro x hx x' hx' y hy hsep
    have hsep' : 2 * (C.dl x x').toReal < (C.dl x' y).toReal := hsep
    have hh0 : 0 ≤ (C.dl x x').toReal := ENNReal.toReal_nonneg
    have hne1 : x' ≠ y := by
      intro h
      rw [← h] at hsep'
      have : (C.dl x' x').toReal = 0 := by
        rw [show C.dl x' x' = 0 from G1.controlDistance_self w C.Xl (hSO hx')]
        rfl
      linarith
    have hne2 : x ≠ y := by
      intro h
      rw [← h] at hsep'
      have : (C.dl x' x).toReal = (C.dl x x').toReal :=
        congrArg ENNReal.toReal (G1.controlDistance_symm C.O w C.Xl x' x)
      linarith
    show |sliceKernel S kk x' y - sliceKernel S kk x y| ≤
      B * (C.dl x x').toReal / (C.dl x' y).toReal ^ (C.G.homogeneousDimension - 1 + 1)
    rw [sliceKernel_of_mem hx' hy hne1, sliceKernel_of_mem hx hy hne2, Nat.sub_add_cancel hQ]
    have := hk.diff x (hSK hx) x' (hSK hx') y (hSK hy) hsep' (hd2 x' hx' y hy)
    exact le_trans (le_add_of_nonneg_right (abs_nonneg _)) this

end LiftedChart

end RothschildStein.P1

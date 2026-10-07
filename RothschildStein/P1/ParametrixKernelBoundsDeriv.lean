-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsSize

/-!
# First and second derivative bounds for kernels away from the pole

The chain rule of the chart gives first and second derivative bounds, in both kernel variables, for
kernels built from weighted symbols. These are the bounds needed for the far part of the Sobolev
interpolation inequality, where the second-order input operator `L̃*_η k` appears (BB pp. 581–583).

Let `A(ξ, η, u)` lie in the weighted symbol class `WtSym` of degree `d` to depth `2` on `L × L`
for every radius, and put `k(ξ, η) = A(ξ, η, Θ(η, ξ))` for `ξ ≠ η` in the compact `L ⊆ U`. Then
with `ρ ≍ d̃(ξ, η)` (lifted-chart field `gauge_comparison`), uniformly over the letters `i, j`:

* `|X̃_{i,ξ} k(ξ, η)| ≤ M d̃(ξ, η)^(d - w_i)`,
* `|X̃_{j,ξ} X̃_{i,ξ} k(ξ, η)| ≤ M d̃(ξ, η)^(d - w_i - w_j)`,

and the same bounds hold for the **input** variable, `X̃_{i,η} k(ξ, η)` and
`X̃_{j,η} X̃_{i,η} k(ξ, η)` (`exists_derivative_bounds_input`). The exponents drop by the letter
weights: `1` for each horizontal letter, `2` for the drift. The proof is the chain rule of the chart
(`ChartExt.fieldDerivative_kernel_eq_Do`, `ChartExt.fieldDerivative_fieldDerivative_kernel_eq_Do`):
`X̃_{i,ξ}[A(ξ, η, Θ(η, ξ))] = (D_i A)(ξ, η, Θ(η, ξ))` with `D_i` lowering the degree by `w_i`
(`ChartExt.Do_class`); the input variable is the output variable of the reflected family
`Â(η, ξ, u) = A(ξ, η, -u)` (`WtSym.reflect`), since `Θ(ξ, η) = -Θ(η, ξ)`.

For `k` of type `ℓ` (`d = ℓ - Q`) this gives the far-part sizes of the Sobolev interpolation inequality: `L̃*_η k` is a second-order
operator in the input variable with `X̃_i X̃_j k` and `X̃_0 k` of size `ρ^(ℓ-Q-2)`; the first-order
adjoint coefficients times `X̃_i k` have size `ρ^(ℓ-Q-1)` and the zeroth-order coefficient times
`k` has size `ρ^(ℓ-Q)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

section Congr

variable {N : ℕ}

/-- The field derivative only sees the germ of the function. -/
theorem fieldDerivative_congr_eventually {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (h : f =ᶠ[𝓝 x] g) :
    fieldDerivative V f x = fieldDerivative V g x := by
  show fderiv ℝ f x (V x) = fderiv ℝ g x (V x)
  rw [h.fderiv_eq]

/-- The iterated field derivative only sees the germ of the function. -/
theorem fieldDerivative_fieldDerivative_congr_eventually {V W : (Fin N → ℝ) → (Fin N → ℝ)}
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (h : f =ᶠ[𝓝 x] g) :
    fieldDerivative V (fieldDerivative W f) x = fieldDerivative V (fieldDerivative W g) x := by
  have h2 : fieldDerivative W f =ᶠ[𝓝 x] fieldDerivative W g := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact fieldDerivative_congr_eventually hy
  exact fieldDerivative_congr_eventually h2

end Congr

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {L : Set (Fin (n + m) → ℝ)}

namespace ChartExt

variable (ex : C.ChartExt L)

include ex

/-- **Derivative bounds in the output variable.** If
`A ∈ WtSym` of degree `d` to depth `2` on `L × L` for every radius, then on the compact `L ⊆ U`,
for `ξ ≠ η`, with `k(ξ, η) = A(ξ, η, Θ(η, ξ))`:
`|X̃_{i,ξ} k| ≤ M d̃(ξ, η)^(d - w_i)` and `|X̃_{j,ξ} X̃_{i,ξ} k| ≤ M d̃(ξ, η)^(d - w_i - w_j)`,
uniformly in the letters `i, j`. -/
theorem exists_derivative_bounds_output (hL : IsCompact L) (hLU : L ⊆ C.U) {d : ℤ}
    {A : KZ (n + m) → ℝ} (hA : ∀ R : ℝ, 0 < R → WtSym C.G (L ×ˢ L) R 2 d A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η → ∀ i j : Fin k,
      |fieldDerivative (C.Xl i) (fun ξ' => A (ξ', η, C.Θ η ξ')) ξ| ≤
        M * (C.dl ξ η).toReal ^ (d - ((w i : ℕ) : ℤ)) ∧
      |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (fun ξ' => A (ξ', η, C.Θ η ξ'))) ξ| ≤
        M * (C.dl ξ η).toReal ^ (d - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) := by
  have hK : IsCompact (L ×ˢ L) := hL.prod hL
  have hD1 : ∀ i : Fin k, ∀ R : ℝ, 0 < R →
      WtSym C.G (L ×ˢ L) R 0 (d - ((w i : ℕ) : ℤ)) (ex.Do i A) := fun i R hR =>
    (ex.Do_class hK hR (hA R hR) i).mono_k (Nat.zero_le 1)
  have hD2 : ∀ i j : Fin k, ∀ R : ℝ, 0 < R →
      WtSym C.G (L ×ˢ L) R 0 (d - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) (ex.Do j (ex.Do i A)) :=
    fun i j R hR => ex.Do_class hK hR (ex.Do_class hK hR (hA R hR) i) j
  choose M₁ hM₁0 hM₁ using fun i : Fin k => C.exists_size_bound_of_wtSym hL hLU (hD1 i)
  choose M₂ hM₂0 hM₂ using fun i j : Fin k =>
    C.exists_size_bound_of_wtSym hL hLU (hD2 i j)
  refine ⟨∑ i, M₁ i + ∑ i, ∑ j, M₂ i j, add_nonneg (Finset.sum_nonneg fun i _ => hM₁0 i)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hM₂0 i j), ?_⟩
  intro ξ hξ η hη hne i j
  have hdpos : 0 < (C.dl ξ η).toReal := C.dl_toReal_pos (hLU hξ) (hLU hη) hne.symm
  have hV : (η, C.Θ η ξ) ∈ ex.V := ex.mem_V η hη ξ hξ
  have hAc : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0} := (hA 1 one_pos).contDiffOn
  have hsum1 : M₁ i ≤ ∑ i, M₁ i + ∑ i, ∑ j, M₂ i j := by
    have h1 : M₁ i ≤ ∑ i', M₁ i' :=
      Finset.single_le_sum (f := M₁) (fun i' _ => hM₁0 i') (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ i, ∑ j, M₂ i j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hM₂0 i j
    linarith
  have hsum2 : M₂ i j ≤ ∑ i, M₁ i + ∑ i, ∑ j, M₂ i j := by
    have h1 : M₂ i j ≤ ∑ j', M₂ i j' :=
      Finset.single_le_sum (f := fun j' => M₂ i j') (fun j' _ => hM₂0 i j') (Finset.mem_univ j)
    have h3 : ∑ j', M₂ i j' ≤ ∑ i', ∑ j', M₂ i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', M₂ i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => hM₂0 i' j') (Finset.mem_univ i)
    have h0 : 0 ≤ ∑ i, M₁ i := Finset.sum_nonneg fun i _ => hM₁0 i
    linarith
  refine ⟨?_, ?_⟩
  · rw [ex.fieldDerivative_kernel_eq_Do hAc (hLU hη) (hLU hξ) hne hV i]
    exact (hM₁ i ξ hξ η hη hne).trans
      (mul_le_mul_of_nonneg_right hsum1 (zpow_pos hdpos _).le)
  · rw [ex.fieldDerivative_fieldDerivative_kernel_eq_Do hAc (hLU hη) (hLU hξ) hne hV i j]
    exact (hM₂ i j ξ hξ η hη hne).trans
      (mul_le_mul_of_nonneg_right hsum2 (zpow_pos hdpos _).le)

/-- **Derivative bounds in the input variable** (via
`Θ(ξ, η) = -Θ(η, ξ)`): under the hypotheses of `exists_derivative_bounds_output`, for `ξ ≠ η` in `L`,
`|X̃_{i,η} k(ξ, η)| ≤ M d̃(ξ, η)^(d - w_i)` and
`|X̃_{j,η} X̃_{i,η} k(ξ, η)| ≤ M d̃(ξ, η)^(d - w_i - w_j)`. -/
theorem exists_derivative_bounds_input (hL : IsCompact L) (hLU : L ⊆ C.U) {d : ℤ}
    {A : KZ (n + m) → ℝ} (hA : ∀ R : ℝ, 0 < R → WtSym C.G (L ×ˢ L) R 2 d A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η → ∀ i j : Fin k,
      |fieldDerivative (C.Xl i) (fun η' => A (ξ, η', C.Θ η' ξ)) η| ≤
        M * (C.dl ξ η).toReal ^ (d - ((w i : ℕ) : ℤ)) ∧
      |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (fun η' => A (ξ, η', C.Θ η' ξ))) η| ≤
        M * (C.dl ξ η).toReal ^ (d - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) := by
  have hAr : ∀ R : ℝ, 0 < R →
      WtSym C.G (L ×ˢ L) R 2 d (fun z : KZ (n + m) => A (z.2.1, z.1, -z.2.2)) := fun R hR =>
    WtSym.reflect (K' := L ×ˢ L) (fun p hp => ⟨hp.2, hp.1⟩) (hA R hR)
  obtain ⟨M, hM0, hM⟩ := ex.exists_derivative_bounds_output hL hLU hAr
  refine ⟨M, hM0, fun ξ hξ η hη hne i j => ?_⟩
  have h := hM η hη ξ hξ hne.symm i j
  have hev : (fun η' => A (ξ, η', C.Θ η' ξ)) =ᶠ[𝓝 η]
      (fun η' => (fun z : KZ (n + m) => A (z.2.1, z.1, -z.2.2)) (η', ξ, C.Θ ξ η')) := by
    filter_upwards [C.isOpen_U.mem_nhds (hLU hη)] with η' hη'
    show A (ξ, η', C.Θ η' ξ) = A (ξ, η', -C.Θ ξ η')
    rw [C.theta_antisymm η' hη' ξ (hLU hξ)]
    simp
  rw [fieldDerivative_congr_eventually hev, fieldDerivative_fieldDerivative_congr_eventually hev,
    C.dl_symm ξ η]
  exact h

/-- **First and second derivative bounds in both variables**:
the conjunction of `exists_derivative_bounds_output` and `exists_derivative_bounds_input` with a
common constant. -/
theorem exists_derivative_bounds (hL : IsCompact L) (hLU : L ⊆ C.U) {d : ℤ}
    {A : KZ (n + m) → ℝ} (hA : ∀ R : ℝ, 0 < R → WtSym C.G (L ×ˢ L) R 2 d A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η → ∀ i j : Fin k,
      (|fieldDerivative (C.Xl i) (fun ξ' => A (ξ', η, C.Θ η ξ')) ξ| ≤
          M * (C.dl ξ η).toReal ^ (d - ((w i : ℕ) : ℤ)) ∧
        |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (fun ξ' => A (ξ', η, C.Θ η ξ'))) ξ| ≤
          M * (C.dl ξ η).toReal ^ (d - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ))) ∧
      (|fieldDerivative (C.Xl i) (fun η' => A (ξ, η', C.Θ η' ξ)) η| ≤
          M * (C.dl ξ η).toReal ^ (d - ((w i : ℕ) : ℤ)) ∧
        |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (fun η' => A (ξ, η', C.Θ η' ξ))) η| ≤
          M * (C.dl ξ η).toReal ^ (d - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ))) := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := ex.exists_derivative_bounds_output hL hLU hA
  obtain ⟨M₂, hM₂0, hM₂⟩ := ex.exists_derivative_bounds_input hL hLU hA
  refine ⟨M₁ + M₂, add_nonneg hM₁0 hM₂0, fun ξ hξ η hη hne i j => ?_⟩
  have hdpos : 0 < (C.dl ξ η).toReal := C.dl_toReal_pos (hLU hξ) (hLU hη) hne.symm
  have hx : ∀ e : ℤ, 0 ≤ (C.dl ξ η).toReal ^ e := fun e => (zpow_pos hdpos e).le
  have hle₁ : M₁ ≤ M₁ + M₂ := le_add_of_nonneg_right hM₂0
  have hle₂ : M₂ ≤ M₁ + M₂ := le_add_of_nonneg_left hM₁0
  obtain ⟨a1, a2⟩ := hM₁ ξ hξ η hη hne i j
  obtain ⟨b1, b2⟩ := hM₂ ξ hξ η hη hne i j
  exact ⟨⟨a1.trans (mul_le_mul_of_nonneg_right hle₁ (hx _)),
    a2.trans (mul_le_mul_of_nonneg_right hle₁ (hx _))⟩,
    ⟨b1.trans (mul_le_mul_of_nonneg_right hle₂ (hx _)),
    b2.trans (mul_le_mul_of_nonneg_right hle₂ (hx _))⟩⟩

end ChartExt

end LiftedChart

end RothschildStein.P1

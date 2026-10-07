-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsRight
public import RothschildStein.P1.RestrictedError

/-!
# Chart bounds, restricted-error bounds and kernel derivative bounds for `P_R` and `F_R^chart`

Composite statements assembling `ParametrixKernelBoundsRight` with the consumers:

* **Restricted-error bounds for `F_R^chart` directly.** For the fixed chart error `F_R^chart = -E_R`
  (`rightChartError`), a compact `K₀ ⊆ U` and an admissible radius `r_*`
  (`IsSmallBallRadius`; it exists when `ξ₀ ∈ interior K₀`), the restricted error
  `𝓕_r f = (F_R^chart E_r f)|_{U_r}` (`E_r f = 1_{U_r} f`, `U_r = driftBall ξ₀ r`) satisfies
  `‖𝓕_r f‖_{L^p} ≤ C r ‖f‖_{L^p}`, `sup |𝓕_r f| ≤ C r sup |f|` and
  `‖𝓕_r f‖_{C^α} ≤ C_α r^(1-α) ‖f‖_{C^α}` for `0 < r < r_*`
  (`exists_rightChartError_lp_bound`, `_sup_bound`, `_holder_bound`).
* **Weighted bounds of the pole data** in the form of the kernel-estimate machinery: the error `E_η Γ`,
  `Z_{i,η} Γ` and `Γ` extend to families `Ψ(ξ, η, u)`, `C¹` off `u = 0`, with `HasWeightedBounds` of
  degrees `1 - Q`, `2 - Q - w_i`, `2 - Q`, which equal the true data at `Θ(η, ξ)`
  (`exists_hasWeightedBounds_rightPoleError`, `_zDeriv`, `hasWeightedBounds_fundamental`).
* **Kernel derivative bounds for the fixed kernels** `P_R` and `F_R^chart`: first and second
  derivative bounds, in the output and the input variable, with the exponent lowered by the letter
  weights (`exists_derivative_bounds_rightParametrixKernel`,
  `exists_derivative_bounds_rightChartErrorKernel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}

variable (C) in
/-- The lifted control ball `U_r = B̃(ξ₀, r)` of the drift chart. -/
abbrev driftBall (ξ₀ : Fin (n + m) → ℝ) (r : ℝ) : Set (Fin (n + m) → ℝ) :=
  rsBall C.O (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) C.Xl ξ₀ r

section Sol

variable {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
  {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ}

/-- The restricted error of the kernel of `F_R^chart` is
`F_R^chart` applied to the zero extension `E_r f = 1_{U_r} f`: `𝓕_r f = F_R^chart E_r f` (on all of
`U`, and `U_r ⊆ U`). -/
theorem restrictedError_rightChartErrorKernel_eq (hr : C.IsSmallBallRadius K₀ ξ₀ rstar)
    {r : ℝ} (hr0 : 0 < r) (hrr : r < rstar) (f : (Fin (n + m) → ℝ) → ℝ) :
    C.restrictedError ξ₀ r (C.rightChartErrorKernel K a b) f =
      fun ξ => C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f) ξ := by
  funext ξ
  have hSU : C.driftBall ξ₀ r ⊆ C.U := fun y hy => hr.subset_U (hr.ball_subset r hr0 hrr hy)
  rw [rightChartError_eq_integral]
  unfold restrictedError
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => ?_)
  rw [Set.indicator_of_notMem (fun h => hη (hSU h)), mul_zero]

end Sol

section Weighted

variable {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {L : Set (Fin (n + m) → ℝ)}

end Weighted

section Deriv

variable {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) {L : Set (Fin (n + m) → ℝ)}

end Deriv

end LiftedChart

end RothschildStein.P1

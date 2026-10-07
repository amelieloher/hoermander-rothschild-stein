-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationAssembly

/-!
# The first Hölder interpolation inequality

The first Hölder interpolation inequality (BB Prop 11.50, Lem 11.51, (11.81)-(11.83), pp. 593-596). For `0 < α < 1`, a fixed
positive-type operator `F` (type `λ ≥ 1`) of a lifted frame and `v ∈ C²` in the chart there are
`γ > 1` and `Cc` independent of `v` and `ε` with
`‖F L̃ v‖_{C^α_{X̃}(V)} ≤ ε ‖L̃ v‖_∞ + Cc ε^{-γ} ‖v‖_∞` for `0 < ε < 1`.

Proof (`FractionalInterpolation*`): split the kernel of each principal term at the scale `h` with a
smooth radial cutoff of a smooth homogeneous norm. The **near kernel** (support at distance
`O(h)`, the lifted kernel bounds with constants independent of `h`) has `C^α` bound `C h^{1-α}` for
`L^∞` data (`FractionalInterpolationNear*`); the **far kernel** is smooth with jets
`O(h^{-M})` (`FractionalInterpolationFarKernel`), one integration by parts moves `L̃` onto it
(`FractionalInterpolationIBP`, `FractionalInterpolationFar`) and the Euclidean Lipschitz bound is
transferred to `d̃` (`FractionalInterpolationEuclid`); the regular remainder is a far kernel without
cutoff (`FractionalInterpolationRegular`); the choice `h = (ε/(2C))^{1/(1-α)}` gives the
statement (`FractionalInterpolationAssembly`). The corollaries for the lifted chart
with drift and without drift, with no further hypothesis, are stated here.

Results: `exists_fractional_interpolation_drift`, `exists_fractional_interpolation_noDrift` (the
inequality for every positive-type operator), with the separate cases
`principal_term_interpolation` and `regular_kernel_interpolation` of
`FractionalInterpolationAssembly`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P2

open RothschildStein.P1

variable {n m st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω} {x₀ : Fin n → ℝ}

/-- **First interpolation inequality, drift chart** (BB Prop 11.50,
Lem 11.51): for the lifted chart with drift and `L̃ = X̃₀ + ∑ᵢ X̃ᵢ²`, every positive-type operator
`T` of a lifted frame, `0 < α < 1` and every `v ∈ C²(O)`,
`‖T L̃ v‖_{C^α(V)} ≤ ε ‖L̃ v‖_{∞,V} + Cc ε^{-γ} ‖v‖_{∞,V}` for `0 < ε < 1`, with `γ > 1` and `Cc`
independent of `ε` and `v`. -/
theorem exists_fractional_interpolation_drift {q : ℕ}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (C : LiftedChart driftWeight st Ω hΩ X x₀ m) {F : KernelFrame (n + m)}
    (hF : C.IsLiftedFrame F) {lam : ℕ} (hlam : 1 ≤ lam) (T : TypeOperator F lam) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ γ Cc : ℝ, 1 < γ ∧ 0 < Cc ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ v : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ 2 v C.O →
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
            (fun x => T.apply (sumSquaresWithDrift C.Xl v) x) ≤
          ENNReal.ofReal ε * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)),
              ENNReal.ofReal |sumSquaresWithDrift C.Xl v x|) +
            ENNReal.ofReal (Cc * ε ^ (-γ)) *
              ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x| := by
  have hw : ∀ i : Fin (q + 1), ((driftWeight i : ℕ+) : ℕ) ≤ 2 := by
    intro i
    unfold driftWeight
    split_ifs <;> simp
  obtain ⟨A, B, hA, hB, h⟩ := sumSquaresWithDrift_eq_diffOp2 (isOpen_liftedDomain C) C.Xl
    (fun i => C.lift_smooth i)
  exact exists_fractional_interpolation hF hw (Cg := (q : ℝ) + 1) (by positivity)
    (liftedVariation_drift C) hlam T hα0 hα1 (Lop := sumSquaresWithDrift C.Xl)
    ⟨A, B, hA, hB, h⟩

/-- **First interpolation inequality, drift-free chart**
(`L̃ = ∑ᵢ X̃ᵢ²`; BB Prop 11.50, Lem 11.51). -/
theorem exists_fractional_interpolation_noDrift {q : ℕ}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) {F : KernelFrame (n + m)}
    (hF : C.IsLiftedFrame F) {lam : ℕ} (hlam : 1 ≤ lam) (T : TypeOperator F lam) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ γ Cc : ℝ, 1 < γ ∧ 0 < Cc ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ v : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ 2 v C.O →
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
            (fun x => T.apply (sumSquares C.Xl v) x) ≤
          ENNReal.ofReal ε * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)),
              ENNReal.ofReal |sumSquares C.Xl v x|) +
            ENNReal.ofReal (Cc * ε ^ (-γ)) *
              ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x| := by
  have hw : ∀ i : Fin q, ((noDriftWeight i : ℕ+) : ℕ) ≤ 2 := by
    intro i
    simp [noDriftWeight]
  obtain ⟨A, B, hA, hB, h⟩ := sumSquares_eq_diffOp2 (isOpen_liftedDomain C) C.Xl
    (fun i => C.lift_smooth i)
  exact exists_fractional_interpolation hF hw (Cg := (q : ℝ) + 1) (by positivity)
    (liftedVariation_noDrift C) hlam T hα0 hα1 (Lop := sumSquares C.Xl) ⟨A, B, hA, hB, h⟩

end RothschildStein.P2

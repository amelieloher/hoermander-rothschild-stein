-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitEstimatesMain

/-!
# Estimates for the singular split and its transpose

Collects the size and difference estimates of BB Prop 11.33 (pp. 572–576, (11.52)–(11.59)):
`K₀` has singular exponent 1, `K₁` has fractional exponents `(1, 1)` (erratum: size `d̃^(1-Q)`,
difference denominator `d̃^Q`), for the split of `K` and for the separate split of the transpose
(exchanged-and-reflected data `(transposeFamily D, Γ*)`). All constants are existential and depend
on the chart, the operator family, the cutoff profile and the pole.

The estimate packages `SplitEstimates` are stated in the powers of the lifted control distance `d̃`
of the kernel estimates; the conversion to the volume-denominator kernel classes of H2 (`d̃^(-Q) ≍ 1/V`) belongs to
the Data D certificate (`H2DataDClass`). The algebraic identity `K = K₀ + K₁`, the transpose identity and the annular cancellation
are in `SingularSplitMain` (`exists_split_and_cancellation`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

variable {C}
variable {L : Set (Fin (n + m) → ℝ)}

section Support

variable {ν : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
  {Γ : (Fin (n + m) → ℝ) → ℝ} {ξ η : Fin (n + m) → ℝ}

/-- The singular part `K₀` vanishes where the cutoff profile vanishes at `Θ(η, ξ)`
(the radial cutoff `φ(ν(Θ(η, ξ)))` is a factor of `K₀`; BB p. 572, support in `ρ < R₀`). -/
theorem splitK0_eq_zero_of_cutoff_eq_zero (h : φ (ν (C.Θ η ξ)) = 0) :
    C.splitK0 ν D Γ φ ξ η = 0 := by
  simp [splitK0, cutoffKernel, h]

/-- The remainder `K₁` vanishes where the cutoff profile vanishes. -/
theorem splitK1_eq_zero_of_cutoff_eq_zero (h : φ (ν (C.Θ η ξ)) = 0) :
    C.splitK1 ν D Γ φ ξ η = 0 := by
  simp [splitK1, cutoffKernel, h]

end Support

end LiftedChart
end RothschildStein.P1

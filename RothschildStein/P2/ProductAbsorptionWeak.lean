-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Leibniz
public import RothschildStein.S.ZeroExtension
public import RothschildStein.S.ContinuousCompactZeroExtension
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.HolderWeakLocality
public import RothschildStein.Definitions.fieldDerivative

/-!
# Weak product rule and zero extension of cutoff products

Part of the zero-extension product estimates (weak product rules; compact-support extension, BB
Cor 2.10).
For `u` with a weak `X_i`-derivative `g` on the open patch `V ⊆ Ω` and a function `c` with
`tsupport c ⊆ K ⊆ V`, `K` compact, the product `u c` (zero outside `K`, hence defined on all of
`Ω` without any value of `u` outside `V`) has the weak `X_i`-derivative `g c + u X_i c` on `Ω`,
and both are continuous on `Ω` when `u`, `g` are continuous on `V` and `c`, `X_i c` are continuous.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
namespace RothschildStein.P2

variable {n m : ℕ}

/-- The support of a field derivative is contained in the support of the function. -/
theorem tsupport_fieldDerivative_subset (Y : (Fin n → ℝ) → (Fin n → ℝ))
    (c : (Fin n → ℝ) → ℝ) : tsupport (fieldDerivative Y c) ⊆ tsupport c := by
  refine closure_minimal ?_ (isClosed_tsupport c)
  intro x hx
  exact support_fderiv_subset ℝ (show x ∈ Function.support (fderiv ℝ c) from fun h =>
    hx (by simp [fieldDerivative, h]))

end RothschildStein.P2

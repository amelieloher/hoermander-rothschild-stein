-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorMeasurable
public import RothschildStein.P1.RestrictedErrorEstimates

/-!
# Small-ball bounds for the restricted error of the right parametrix

Entry point for the `RestrictedError*` modules. For a kernel `kk` on a lifted chart `C` with the kernel
bounds `RestrictedKernelBounds K₀ kk A B` (size `A d̃^(1-Q)`, difference
`B d̃(ξ, ξ') / d̃(ξ', η)^Q`) on a compact `K₀ ⊆ U`, and an admissible radius `r_* ≤ 1`
(`IsSmallBallRadius`, existing when `ξ₀ ∈ interior K₀`: `exists_isSmallBallRadius`), the restricted
error `𝓕_r f = (∫ kk(·, η) E_r f(η) dη)|_{U_r}`, `U_r = rsBall C.O w C.Xl ξ₀ r`, `0 < r < r_*`,
satisfies (BB pp. 606–607):

* `exists_restrictedError_lp_bound`: `‖𝓕_r f‖_{L^p(U_r)} ≤ C r ‖f‖_{L^p(U_r)}`, `1 ≤ p < ∞`;
* `exists_restrictedError_sup_bound`, `exists_restrictedError_iSup_bound`:
  `‖𝓕_r f‖_∞ ≤ C r ‖f‖_∞`;
* `exists_restrictedError_holder_bound`: `‖𝓕_r f‖_{C^α(U_r)} ≤ C_α r^(1-α) ‖f‖_{C^α(U_r)}`,
  `0 < α < 1`, in terms of `holderENorm` with `C.dl`.

Modules: `RestrictedErrorShell` (dyadic shell integrals), `RestrictedErrorSlice` (row/column, sup,
`L^p`), `RestrictedErrorHolder` (near/far splitting), `RestrictedErrorChart` (small-ball radius),
`RestrictedErrorKernel` (kernel hypotheses), `RestrictedErrorEstimates` (they follow from the kernel estimates),
`RestrictedErrorDef`, `RestrictedErrorLp`, `RestrictedErrorBounds`, `RestrictedErrorMeasurable`.
-/

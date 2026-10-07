-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityLp
public import RothschildStein.P2.SolvabilityHolder
public import RothschildStein.P2.SolvabilityIdentity
public import RothschildStein.P2.SolvabilitySolution

/-!
# Local solvability by contraction mapping (BB pp. 605-608, Prop 11.61)

Entry point for the `Solvability*` modules. On a lifted drift chart with fixed cutoffs `a, b` and centre
`ξ₀` (`a = 1` near `ξ₀`), `U_r = B̃(ξ₀, r)`, `E_r f = 1_{U_r} f`, and the restricted error
`𝓕_r f = (F_R^chart E_r f)|_{U_r}` is the restricted error term:

* The `L^p` contraction (`SolvabilityLpFixed`, `SolvabilityLp`): `𝓕_r` is a bounded operator of
  `L^p(U_r)` of norm `≤ C_L r` for all `1 ≤ p < ∞` (`exists_rightChartError_lpBoundedOperator`);
  for `r < r₀`, `C_L r ≤ 1/2`, `f ↦ g + 𝓕_r f` is a contraction of `Lp ℝ p (volume.restrict U_r)`
  (`exists_lp_contraction`) and the unique fixed point satisfies `‖f‖_p ≤ 2 ‖g‖_p`
  (`exists_lp_fixedPoint`).
* The Hölder contraction (`SolvabilityHolderSpace`, `SolvabilityHolderFixed`,
  `SolvabilityHolder`): the Banach space `C^α(U_r)` (`BoundedHolder`, completeness from
  BB Prop 2.15); `𝓕_r` is a bounded operator of norm `≤ C_α r^(1-α)`
  (`exists_rightChartError_holderBoundedOperator`); the contraction and the fixed point
  `f = g + 𝓕_r f`, `‖f‖_{C^α} ≤ 2 ‖g‖_{C^α}` (`exists_holder_contraction`,
  `exists_holder_fixedPoint`).
* The consequence `L̃ v = g` on `U_r` in distributions for `v = P_R E_r f`
  (`SolvabilityIdentity`, `SolvabilitySolution`): it holds whenever `f` is a test function
  supported in `U_r` (`rightParametrix_solves_of_test`); for `L^p` and Hölder data assuming
  the hypothesis `RightLpIdentity`
  (`rightParametrix_solves_of_lpIdentity`, `rightParametrix_solves_holder_of_lpIdentity`,
  `exists_lp_solution_of_lpIdentity`, `exists_holder_solution_of_lpIdentity`).
-/

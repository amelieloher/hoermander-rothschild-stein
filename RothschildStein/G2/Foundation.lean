-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.AnalyticStructure
public import RothschildStein.G2.TopologicalGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

/-! The homogeneous group law, triangular polynomial
structure, inversion, and Lebesgue invariance (BB Definitions 3.1–3.2, pp. 94–95;
Theorem 3.6, pp. 96–98; Proposition 3.7, p. 98). -/

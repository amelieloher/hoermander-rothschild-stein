-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.GaugeBalls
public import RothschildStein.G2.Gauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open TopologicalSpace

/-- The open domain of a smooth-gauge quasiball used in local weak norms. -/
def quasiballDomain {n : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin n → ℝ) (r : ℝ) : Opens (Fin n → ℝ) :=
  ⟨G2.gaugeBall G ν x₀ r, G2.isOpen_gaugeBall G ν.gauge x₀ r⟩

end RothschildStein.H3

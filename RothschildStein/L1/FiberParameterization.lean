-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ParameterizedChartInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- A jointly smooth horizontal inverse gives a jointly smooth
vertical fiber parametrization by composition (BB pp. 520–521). -/
theorem contDiffOn_fiber_parameterization {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U V : Set (E × F)} (Φ : E × F → E × F) (θ : E × F → E)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U) (hθ : ContDiffOn ℝ (⊤ : ℕ∞) θ V)
    (hmap : ∀ p ∈ V, (θ p, p.2) ∈ U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : E × F => (Φ (θ p, p.2)).2) V :=
  (hΦ.comp (hθ.prodMk contDiffOn_snd) hmap).snd

/-- The fiber parametrization is injective because the full
chart is injective and the horizontal coordinate is fixed. -/
theorem injOn_fiber_parameterization {E F : Type*} {U : Set (E × F)} {V : Set F}
    (Φ : E × F → E × F) (θ : E × F → E) (y : E)
    (hinj : InjOn Φ U) (hmap : ∀ v ∈ V, (θ (y, v), v) ∈ U)
    (hbase : ∀ v ∈ V, (Φ (θ (y, v), v)).1 = y) :
    InjOn (fun v => (Φ (θ (y, v), v)).2) V := by
  intro v hv v' hv' he
  have hfull : Φ (θ (y, v), v) = Φ (θ (y, v'), v') :=
    Prod.ext ((hbase v hv).trans (hbase v' hv').symm) he
  exact congrArg Prod.snd (hinj (hmap v hv) (hmap v' hv') hfull)

end RothschildStein.L1

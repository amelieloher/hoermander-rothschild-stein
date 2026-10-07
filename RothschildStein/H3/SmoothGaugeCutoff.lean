-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballProfile
public import RothschildStein.G2.Gauge
public import RothschildStein.G2.InvariantFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Filter
open scoped Topology

/-- Composing the profile with a smooth homogeneous gauge is smooth
also at zero: the profile is constant on a neighborhood of the origin. -/
theorem contDiff_radial_quasiballProfile {N : ℕ} {G : HomogeneousGroup N}
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => quasiballProfile t s (ν x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : ν 0 = 0 := (ν.gauge.2.2.1 0).mpr rfl
    have hU : {y | ν y < t} ∈ 𝓝 (0 : Fin N → ℝ) :=
      (isOpen_lt ν.gauge.1 continuous_const).mem_nhds (by
        change ν 0 < t
        rw [hz]
        exact ht)
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hU] with y hy
    exact quasiballProfile_one hts hy.le
  · have hv : ContDiffAt ℝ (⊤ : ℕ∞) ν x :=
      hν.contDiffAt (isOpen_compl_singleton.mem_nhds hx)
    exact (quasiballProfile_contDiff t s).contDiffAt.comp x hv

/-- The cutoff around an arbitrary group center uses the smooth
homogeneous gauge and left translation, rather than a control norm. -/
def smoothQuasiballCutoff {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin N → ℝ) (t s : ℝ) (y : Fin N → ℝ) : ℝ :=
  quasiballProfile t s (ν (G.mul (G.inv x₀) y))

/-- The translated cutoff is smooth at every point. -/
theorem smoothQuasiballCutoff_contDiff {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (x₀ : Fin N → ℝ)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothQuasiballCutoff G ν x₀ t s) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin N → ℝ => quasiballProfile t s (ν (G.mul (G.inv x₀) y)))
  exact (contDiff_radial_quasiballProfile ν hν ht hts).comp
    (G2.contDiff_leftTranslation G (G.inv x₀))

end RothschildStein.H3

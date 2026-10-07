-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothGaugeCutoff
public import RothschildStein.G2.GaugeBalls
public import RothschildStein.G2.NormConstruction
public import Mathlib.Topology.Algebra.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set

/-- The translated cutoff is between zero and one. -/
theorem smoothQuasiballCutoff_range {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (x₀ y : Fin N → ℝ) (t s : ℝ) :
    0 ≤ smoothQuasiballCutoff G ν x₀ t s y ∧ smoothQuasiballCutoff G ν x₀ t s y ≤ 1 :=
  quasiballProfile_range t s _

/-- The translated cutoff equals one on the entire inner quasi-ball. -/
theorem smoothQuasiballCutoff_one {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin N → ℝ) {t s : ℝ} (hts : t < s) :
    EqOn (smoothQuasiballCutoff G ν x₀ t s) (fun _ => 1) (G2.gaugeBall G ν x₀ t) := by
  intro y hy
  exact quasiballProfile_one hts hy.le

/-- The topological support lies inside the closed intermediate
quasi-ball, giving a strict support buffer before the outer radius. -/
theorem smoothQuasiballCutoff_tsupport {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin N → ℝ) {t s : ℝ} (hts : t < s) :
    tsupport (smoothQuasiballCutoff G ν x₀ t s) ⊆
      G2.gaugeClosedBall G ν x₀ ((t + s) / 2) := by
  change closure (Function.support (smoothQuasiballCutoff G ν x₀ t s)) ⊆ _
  apply closure_minimal ?_ (G2.isCompact_gaugeClosedBall G ν.gauge x₀ ((t + s) / 2)).isClosed
  intro y hy
  by_contra hnot
  have hρ : (t + s) / 2 ≤ ν (G.mul (G.inv x₀) y) := by
    change ¬ν (G.mul (G.inv x₀) y) ≤ (t + s) / 2 at hnot
    exact (lt_of_not_ge hnot).le
  exact hy (quasiballProfile_zero hts hρ)

/-- The constructed cutoff has compact support in the original
Euclidean topology of the group. -/
theorem smoothQuasiballCutoff_compact {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin N → ℝ) {t s : ℝ} (hts : t < s) :
    HasCompactSupport (smoothQuasiballCutoff G ν x₀ t s) :=
  (G2.isCompact_gaugeClosedBall G ν.gauge x₀ ((t + s) / 2)).of_isClosed_subset
    (isClosed_tsupport _) (smoothQuasiballCutoff_tsupport G ν x₀ hts)

/-- The closed intermediate quasi-ball is contained in the open
outer quasi-ball, with no comparison to the control metric required. -/
theorem intermediate_quasiball_subset {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin N → ℝ) {t s : ℝ} (hts : t < s) :
    G2.gaugeClosedBall G ν x₀ ((t + s) / 2) ⊆ G2.gaugeBall G ν x₀ s := by
  intro y hy
  change ν (G.mul (G.inv x₀) y) ≤ (t + s) / 2 at hy
  change ν (G.mul (G.inv x₀) y) < s
  exact hy.trans_lt (by linarith)

end RothschildStein.H3

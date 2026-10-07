-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlMetric
public import RothschildStein.H2.LocDoubling
public import RothschildStein.G2.MeasureConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The fixed locally doubling setting uses radii 1, 19, 37, κ = 3,
and doubling constant 2^Q (BB pp. 357–359). -/
def groupSetting (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric) :
    letI := gaugeMetric G ν h1 hsym
    H2.LocDoubling (ControlCarrier N) := by
  letI := gaugeMetric G ν h1 hsym
  have hb (x : ControlCarrier N) (r : ℝ) : ball x r = gaugeBall G ν x r := rfl
  have hcpt : IsCompact (closure (ball (0 : ControlCarrier N) 37)) := by
    have hk : IsCompact (closedBall (0 : ControlCarrier N) 37) := by
      change IsCompact (gaugeClosedBall G ν (0 : Fin N → ℝ) 37)
      exact isCompact_gaugeClosedBall G ν.gauge 0 37
    exact hk.of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  letI : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  refine {
    μ := volume
    Ω₀ := ball 0 1
    Ω₁ := ball 0 19
    Ω₂ := ball 0 37
    open₀ := isOpen_ball
    open₁ := isOpen_ball
    open₂ := isOpen_ball
    sub₀₁ := ball_subset_ball (by norm_num)
    sub₁₂ := ball_subset_ball (by norm_num)
    cpt := hcpt
    κ := 3
    κ_pos := by norm_num
    incl₀ := ?_
    incl₁ := ?_
    C_D := (2 : ℝ) ^ G.homogeneousDimension
    one_lt_C_D := ?_
    doubling := ?_
    noAtoms := fun x => measure_singleton x
    finΩ₂ := ?_
  }
  · intro y hy z hz
    change dist z 0 < 19
    have hy' : dist y 0 < 1 := hy
    have hz' : dist z y ≤ 18 := by
      change dist z y ≤ 6 * 3 at hz
      norm_num at hz
      exact hz
    exact (dist_triangle z y 0).trans_lt (by linarith)
  · intro y hy z hz
    change dist z 0 < 37
    have hy' : dist y 0 < 19 := hy
    have hz' : dist z y ≤ 18 := by
      change dist z y ≤ 6 * 3 at hz
      norm_num at hz
      exact hz
    exact (dist_triangle z y 0).trans_lt (by linarith)
  · exact one_lt_pow₀ (by norm_num) (homogeneousDimension_pos G).ne'
  · intro x _ r hr _
    simp only [hb]
    refine ⟨volume_gaugeBall_pos G ν.gauge x (by positivity), ?_,
      (volume_gaugeBall_ne_top G ν.gauge x r).lt_top⟩
    exact (volume_gaugeBall_doubling ν.gauge x hr).le
  · rw [hb]
    exact (volume_gaugeBall_ne_top G ν.gauge 0 37).lt_top

end RothschildStein.H3

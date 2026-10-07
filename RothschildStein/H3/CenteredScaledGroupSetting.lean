-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GroupSetting

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- At every center and positive radius, the corrected balls
B(z,r), B(z,19r), B(z,37r) and kappa=3r satisfy the actual H2 buffer
and doubling requirements (BB p. 350, corrected setting). -/
def centeredScaledGroupSetting (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (z : ControlCarrier N) (r : ℝ) (hr : 0 < r) :
    letI := gaugeMetric G ν h1 hsym
    H2.LocDoubling (ControlCarrier N) := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  have hb (x : ControlCarrier N) (s : ℝ) : ball x s = gaugeBall G ν x s := rfl
  have hcpt : IsCompact (closure (ball z (37 * r))) := by
    have hk : IsCompact (closedBall z (37 * r)) := by
      change IsCompact (gaugeClosedBall G ν (z : Fin N → ℝ) (37 * r))
      exact isCompact_gaugeClosedBall G ν.gauge z (37 * r)
    exact hk.of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  refine {
    μ := volume
    Ω₀ := ball z r
    Ω₁ := ball z (19 * r)
    Ω₂ := ball z (37 * r)
    open₀ := isOpen_ball
    open₁ := isOpen_ball
    open₂ := isOpen_ball
    sub₀₁ := ball_subset_ball (by linarith)
    sub₁₂ := ball_subset_ball (by linarith)
    cpt := hcpt
    κ := 3 * r
    κ_pos := by positivity
    incl₀ := ?_
    incl₁ := ?_
    C_D := (2 : ℝ) ^ G.homogeneousDimension
    one_lt_C_D := one_lt_pow₀ (by norm_num) (homogeneousDimension_pos G).ne'
    doubling := ?_
    noAtoms := fun x => measure_singleton x
    finΩ₂ := ?_
  }
  · intro y hy x hx
    change dist x z < 19 * r
    have hy' : dist y z < r := hy
    have hx' : dist x y ≤ 18 * r := by
      change dist x y ≤ 6 * (3 * r) at hx
      linarith
    exact (dist_triangle x y z).trans_lt (by linarith)
  · intro y hy x hx
    change dist x z < 37 * r
    have hy' : dist y z < 19 * r := hy
    have hx' : dist x y ≤ 18 * r := by
      change dist x y ≤ 6 * (3 * r) at hx
      linarith
    exact (dist_triangle x y z).trans_lt (by linarith)
  · intro x _ s hs _
    simp only [hb]
    exact ⟨volume_gaugeBall_pos G ν.gauge x (by positivity),
      (volume_gaugeBall_doubling ν.gauge x hs).le,
      (volume_gaugeBall_ne_top G ν.gauge x s).lt_top⟩
  · rw [hb]
    exact (volume_gaugeBall_ne_top G ν.gauge z (37 * r)).lt_top

end RothschildStein.H3

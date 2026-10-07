-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.EnlargedGaugeBallSolver
public import RothschildStein.Provider.GroupRegularityInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The exact control ball at the origin is the constructed control
norm sublevel set, with the order of both group factors respected. -/
theorem control_origin_ball_eq_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields) {R : ℝ} (hR : 0 < R) :
    {x | controlDistance univ driftWeight H.fields 0 x < ENNReal.ofReal R} = {x | C.norm x < R} := by
  ext x
  change controlDistance univ driftWeight H.fields 0 x < ENNReal.ofReal R ↔ C.norm x < R
  rw [C.distance_eq]
  change ENNReal.ofReal (C.norm (G.mul (G.inv x) 0)) < ENNReal.ofReal R ↔ C.norm x < R
  rw [G2.mul_zero, C.symmetric, ENNReal.ofReal_lt_ofReal_iff hR]

/-- The exact shared enlarged
ball solver interface follows from the actual Holder potential solver.
The larger ball and constant precede every zero-extended source. -/
theorem holderBallTransfer_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm) (ν : G2.HomogeneousNorm G) :
    Provider.HolderBallTransfer G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) ν := by
  intro α hα hα1 R hR
  let a := Real.toNNReal α
  have hae : (a : ℝ) = α := Real.coe_toNNReal _ hα.le
  have ha : 0 < a := Real.toNNReal_pos.mpr hα
  have ha1 : (a : ℝ) < 1 := by rw [hae]; exact hα1
  obtain ⟨S, hS, V, hV, hcontains, A, hA, hsolve⟩ :=
    enlarged_gauge_ball_solver_of_controlNorm G H K hQ C φ ν ha ha1 hR
  have hball := control_origin_ball_eq_of_controlNorm G H C hR
  refine ⟨S, hS, V, hV, ?_, A, hA, ?_⟩
  · rw [hball]
    exact hcontains
  · intro Ω hΩ f hf hzero
    rw [hball] at hΩ
    have hf' : memHolderXCompact driftWeight H.fields (controlDistance univ driftWeight H.fields) Ω 0 a f := by
      simpa only [hae] using hf
    obtain ⟨u, hu, heq, hn⟩ := hsolve Ω hΩ f hf' hzero
    exact ⟨u, by simpa only [hae] using hu, heq, by simpa only [hae] using hn⟩

end RothschildStein.H3

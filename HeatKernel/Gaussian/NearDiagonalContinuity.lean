-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.ConvolutionLipschitz

/-! # Uniform unit-time positivity near the diagonal

Continuity and positivity at the identity give a positive neighborhood.
Left-translation covariance makes its radius independent of the center.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric RothschildStein Filter
open scoped Topology
namespace HeatKernel.Gaussian
set_option backward.isDefEq.respectTransparency false

/-- A continuous positive kernel section and left covariance give a uniform
unit-time lower bound on a neighborhood of the diagonal. -/
theorem exists_unit_near_diagonal_radius_of_continuity {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (p : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hcont : Continuous (fun z : CarnotPoint G hq hqpos hspan ↦ p 0 z))
    (hpos : 0 < p 0 0)
    (hleft : ∀ a x y, p (G.mul a x) (G.mul a y) = p x y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x y : CarnotPoint G hq hqpos hspan,
      dist x y ≤ ε → p 0 0 / 2 ≤ p x y := by
  let o : CarnotPoint G hq hqpos hspan := (0 : Fin N → ℝ)
  have hn : {z : CarnotPoint G hq hqpos hspan | p 0 0 / 2 < p 0 z} ∈ 𝓝 o :=
    hcont.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r / 2, by positivity, ?_⟩
  intro x y hxy
  let z : CarnotPoint G hq hqpos hspan := G.mul (G.inv x) y
  have hd : dist z o = dist x y := by
    have h := CarnotPoint.dist_leftTranslation G hq hqpos hspan (G.inv x) y x
    simpa only [G2.inv_mul, dist_comm] using h
  have hz : z ∈ ball o r := by
    rw [mem_ball, hd]
    linarith
  have hl := hleft (G.inv x) x y
  rw [G2.inv_mul] at hl
  exact (hb hz).le.trans_eq hl

end HeatKernel.Gaussian

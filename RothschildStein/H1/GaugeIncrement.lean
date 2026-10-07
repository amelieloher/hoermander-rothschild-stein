-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.GroupIncrement
public import RothschildStein.H1.NestedCutoffs
public import RothschildStein.G2.AnalyticStructure
public import RothschildStein.G2.EuclideanComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Uniform left and right group increments of a compact
C¹ function are bounded by the homogeneous gauge. A joint compact
cutoff provides a global Lipschitz bound (BB Prop 6.29, pp. 276–278). -/
theorem exists_gaugeIncrement_bound
    {ν ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x w, ν w ≤ r₀ →
      |ψ (G.mul x w) - ψ x| + |ψ (G.mul w x) - ψ x| ≤ C * ν w := by
  let U : Opens (Fin N → ℝ) := ⟨univ, isOpen_univ⟩
  obtain ⟨η, W, _, hKW, hW, _⟩ := exists_test_eq_one_near_compact U
    (G2.isCompact_gauge_le hν r₀) (subset_univ _)
  have he (w : Fin N → ℝ) (hw : ν w ≤ r₀) : η w = 1 := hW w (hKW hw)
  have hν0 : ν (0 : Fin N → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
  have he0 : η (0 : Fin N → ℝ) = 1 := he 0 (by simpa only [hν0] using hr₀.le)
  have hηc : ContDiff ℝ 1 (η : (Fin N → ℝ) → ℝ) := η.contDiff.of_le (by simp)
  have hR := exists_rightGroup_increment_bound G (W := {w | ν w ≤ r₀}) hc hs hηc η.hasCompactSupport he0 he
  have hL := exists_leftGroup_increment_bound G (W := {w | ν w ≤ r₀}) hc hs hηc η.hasCompactSupport he0 he
  obtain ⟨CR, hCR, hRb⟩ := hR
  obtain ⟨CL, hCL, hLb⟩ := hL
  obtain ⟨a, _, ha, _, hcomp⟩ := G2.gauge_sublevel_norm_comparison hν r₀
  refine ⟨(CR + CL) / a, div_nonneg (add_nonneg hCR hCL) ha.le, ?_⟩
  intro x w hw
  have hb := (hcomp w hw).1
  have hsum := add_le_add (hRb x w hw) (hLb x w hw)
  have hnorm : ‖w‖ ≤ ν w / a := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hb)
  calc
    _ ≤ (CR + CL) * ‖w‖ := by linarith
    _ ≤ (CR + CL) * (ν w / a) := mul_le_mul_of_nonneg_left hnorm (add_nonneg hCR hCL)
    _ = ((CR + CL) / a) * ν w := by ring

end RothschildStein.H1

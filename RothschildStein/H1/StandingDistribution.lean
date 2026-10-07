-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalFundamentalDistribution
public import RothschildStein.H1.ReversedOperator
public import RothschildStein.H1.BarrierRate
public import RothschildStein.H1.FundamentalDictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The local order-zero fundamental distribution for the standing
operator, with the group transpose test (BB Prop 6.2, p. 250). -/
theorem StandingHypotheses.exists_localFundamentalDistribution
    (H : StandingHypotheses G q) (Ω : Opens (Fin N → ℝ))
    (hΩ : Bornology.IsBounded (Ω : Set (Fin N → ℝ)))
    {d : ℝ} (hd : 0 ≤ d)
    (hstrip : ∀ x ∈ Ω, -d < x (firstIndex G) ∧ x (firstIndex G) < d) :
    ∃ T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ,
      ‖T‖ ≤ Real.exp (2 * barrierRate G H * d) - 1 ∧
      ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
        smoothOrderZeroDistribution Ω T (sumSquaresWithDriftTransposeTest Ω H.fields
          (fun i => (H.fields_smooth G i).contDiffOn) φ) = φ 0 := by
  let R := H.reverseDrift G
  obtain ⟨T, hT, he⟩ := exists_localFundamentalDistribution_of_barrier Ω R.fields
    (fun i => (R.fields_smooth G i).contDiffOn) (firstIndex G)
    (barrierRate_pos G R).le hd (R.operator_barrier G) hΩ hstrip
  have hr : barrierRate G R = barrierRate G H := by
    unfold barrierRate R
    rw [H.reverseDrift_squareSum G]
  refine ⟨T, by simpa only [hr] using hT, fun φ => ?_⟩
  have htest : sumSquaresTest Ω R.fields (fun i => (R.fields_smooth G i).contDiffOn) φ =
      sumSquaresWithDriftTransposeTest Ω H.fields (fun i => (H.fields_smooth G i).contDiffOn) φ := by
    ext x
    rw [sumSquaresTest_apply, H.transposeTest_apply G]
    exact H.reverseDrift_operator G φ φ.contDiff x
  rw [← htest]
  exact he φ

/-- The unit sup-norm ball is the local cube used in
BB Thm 6.3 (printed pp. 251–253). -/
def localUnitCube : Opens (Fin N → ℝ) :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The local cube lies in the required first-coordinate slab (BB p. 250). -/
theorem localUnitCube_slab (x : Fin N → ℝ) (hx : x ∈ (localUnitCube : Opens (Fin N → ℝ))) :
    -1 < x (firstIndex G) ∧ x (firstIndex G) < 1 := by
  change x ∈ Metric.ball (0 : Fin N → ℝ) 1 at hx
  have hn : ‖x‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hj0 : |x (firstIndex G)| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x (firstIndex G)
  have hj : |x (firstIndex G)| < 1 := hj0.trans_lt hn
  exact abs_lt.mp hj

/-- The local cube has the source's order-zero fundamental
distribution and bound exp(2 gamma_0), obtained from the stronger barrier
constant exp(2 gamma_0)-1 (BB Prop 6.2, p. 250). -/
theorem StandingHypotheses.exists_cubeFundamentalDistribution (H : StandingHypotheses G q) :
    ∃ T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ,
      ‖T‖ ≤ Real.exp (2 * barrierRate G H) ∧
      ∀ φ : TestFunction localUnitCube ℝ (⊤ : ℕ∞),
        smoothOrderZeroDistribution localUnitCube T
          (sumSquaresWithDriftTransposeTest localUnitCube H.fields
            (fun i => (H.fields_smooth G i).contDiffOn) φ) = φ 0 := by
  obtain ⟨T, hT, he⟩ := H.exists_localFundamentalDistribution G localUnitCube
    Metric.isBounded_ball (by norm_num : (0 : ℝ) ≤ 1) (localUnitCube_slab G)
  refine ⟨T, ?_, he⟩
  have Ht : ‖T‖ ≤ Real.exp (2 * barrierRate G H) - 1 := by simpa only [mul_one] using hT
  linarith

end RothschildStein.H1

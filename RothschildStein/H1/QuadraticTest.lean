-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.NestedCutoffs
public import RothschildStein.H1.QuadraticBarrier
public import RothschildStein.H1.ReversedOperator
public import RothschildStein.Definitions.testMultiplierOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A field derivative depends only on the function's germ
near the point, with no differentiability required outside that germ. -/
theorem fieldDerivative_eventuallyEq
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {f g : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} (he : f =ᶠ[𝓝 x] g) :
    fieldDerivative V f =ᶠ[𝓝 x] fieldDerivative V g := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  change fderiv ℝ f y (V y) = fderiv ℝ g y (V y)
  rw [hy]

/-- The actual compact quadratic test has zero value and
nonzero operator value at the origin (BB (6.6)–(6.8), pp. 251–253). -/
theorem StandingHypotheses.exists_quadraticTest (H : StandingHypotheses G q)
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω) :
    ∃ φ : TestFunction Ω ℝ (⊤ : ℕ∞), φ 0 = 0 ∧
      sumSquaresWithDriftTranspose H.fields φ 0 ≠ 0 := by
  obtain ⟨_, η, hη, _, _, _⟩ := exists_nestedKernelCutoffs Ω h0
  let f : (Fin N → ℝ) → ℝ := fun y => (y (firstIndex G)) ^ 2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_apply ℝ ℝ _).pow 2
  let φ := testMultiplierOn Ω f hf.contDiffOn η
  have he : (φ : (Fin N → ℝ) → ℝ) =ᶠ[𝓝 (0 : Fin N → ℝ)] f := by
    filter_upwards [hη] with x hx
    change η x * f x = f x
    change η x = 1 at hx
    rw [hx, one_mul]
  have hd (i : Fin (q + 1)) := fieldDerivative_eventuallyEq (H.fields i) he
  have hdd (i : Fin (q + 1)) := fieldDerivative_eventuallyEq (H.fields i) (hd i)
  have hop : sumSquaresWithDrift H.fields φ 0 = sumSquaresWithDrift H.fields f 0 := by
    simp only [sumSquaresWithDrift, (hd 0).self_of_nhds]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (hdd i.succ).self_of_nhds
  have htrans : sumSquaresWithDriftTranspose H.fields φ 0 =
      sumSquaresWithDrift H.fields φ 0 := by
    rw [H.sumSquaresTranspose_formula G φ φ.contDiff]
    have hz : fieldDerivative (H.fields 0) φ 0 = 0 := by
      rw [(hd 0).self_of_nhds]
      simp only [f, fieldDerivative_square_coordinate, Pi.zero_apply, mul_zero, zero_mul]
    simp only [sumSquaresWithDrift, hz, neg_zero, zero_add]
  refine ⟨φ, ?_, ?_⟩
  · change η 0 * ((0 : Fin N → ℝ) (firstIndex G)) ^ 2 = 0
    simp
  · rw [htrans, hop, H.operator_square G 0]
    exact (mul_pos (by norm_num) (H.horizontalFirstSquareSum_pos G)).ne'

end RothschildStein.H1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevInterpolationSingle

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal BigOperators

/-- The horizontal-family weak Sobolev interpolation estimate under the
global flow and density hypotheses. -/
theorem sobolev_interpolation_horizontal_of_flow_and_density {n m q : ℕ} (G : HomogeneousGroup n)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (ι : Fin q → Fin m) (hι : ∀ i, (w (ι i) : ℕ) = 1)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => X (ι i)))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX w X ⊤ 2 p u → Nonempty (SobolevWordApproximation w X p u))
    {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X ⊤ 2 p u)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ i, weakWordENorm X ⊤ [ι i] p u) ≤
      ENNReal.ofReal (2*(q : ℝ)/ε)*eLpNorm u p volume +
        ENNReal.ofReal (ε/2)*(∑ i, weakWordENorm X ⊤ [ι i,ι i] p u) := by
  apply interpolation_sum_fields
  intro i
  exact sobolev_interpolation_single_of_flow_and_density G w X hX (ι i) (hι i)
    (E i) (hE i) (hE0 i) (hflow i) hp hpt hdensity hu hε

end RothschildStein.H3

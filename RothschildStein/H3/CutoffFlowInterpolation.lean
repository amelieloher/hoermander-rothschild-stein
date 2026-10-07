-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffSobolevGlobal
public import RothschildStein.H3.SobolevInterpolationFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- Global interpolation applies to an interior cutoff of local Sobolev
data under the global flow and density hypotheses (BB Lemma 8.42, p. 371). -/
theorem cutoff_interpolation_of_flow_and_density {n m q : ℕ}
    (G : HomogeneousGroup n) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (ι : Fin q → Fin m) (hι : ∀ i, (w (ι i) : ℕ) = 1)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => X (ι i)))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX w X ⊤ 2 p u →
      Nonempty (SobolevWordApproximation w X p u))
    (Ω : Opens (Fin n → ℝ)) {u : (Fin n → ℝ) → ℝ}
    (hu : memSobolevX w X Ω 2 p u)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) {ε : ℝ} (hε : 0 < ε) :
    (∑ i, weakWordENorm X ⊤ [ι i] p (fun x => u x * φ x)) ≤
      ENNReal.ofReal (2*(q : ℝ)/ε)*eLpNorm (fun x => u x * φ x) p volume +
        ENNReal.ofReal (ε/2)*
          (∑ i, weakWordENorm X ⊤ [ι i,ι i] p (fun x => u x * φ x)) := by
  exact sobolev_interpolation_horizontal_of_flow_and_density G w X hX ι hι E hE hE0 hflow
    hp hpt hdensity
    (cutoff_memSobolevX_global w X Ω (fun i => (hX i).contDiffOn) 2 p hp u hu φ) hε

end RothschildStein.H3

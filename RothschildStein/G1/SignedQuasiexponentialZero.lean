-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlatParameterDerivative
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RothschildStein.G1

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Signed quasiexponential in the product-factor coordinates;
τ contains the weighted absolute powers of time (BB pp. 32–34). -/
def signedFactoredMap (Hp Hm : P × E → E) (τ : ℝ → P) (q : ℝ × E) : E :=
  q.2 + if 0 ≤ q.1 then q.1 • Hp (τ q.1, q.2) else |q.1| • Hm (τ q.1, q.2)

omit [NormedSpace ℝ P] in
/-- Matching opposite coefficients gives the full joint derivative
at zero time, using continuity of the weighted powers alone. No derivative
of τ at zero is assumed (BB Thm 1.48, pp. 32–34). -/
theorem signedFactoredMap_hasFDerivAt_zero
    (Hp Hm : P × E → E) (τ : ℝ → P) (x : E)
    (hτ : ContinuousAt τ 0) (hτ0 : τ 0 = 0)
    (hHp : ContinuousAt Hp (0, x)) (hHm : ContinuousAt Hm (0, x))
    (hmatch : -Hm (0, x) = Hp (0, x)) :
    HasFDerivAt (signedFactoredMap Hp Hm τ)
      ((ContinuousLinearMap.snd ℝ ℝ E) +
        (ContinuousLinearMap.toSpanSingleton ℝ (Hp (0, x))).comp
          (ContinuousLinearMap.fst ℝ ℝ E)) (0, x) := by
  classical
  let H : ℝ × E → E := fun q =>
    if 0 ≤ q.1 then Hp (τ q.1, q.2) else -Hm (τ q.1, q.2)
  have hf : ContinuousAt (Prod.fst : ℝ × E → ℝ) (0, x) := continuousAt_fst
  have ht : ContinuousAt (fun q : ℝ × E => τ q.1) (0, x) := by
    simpa only [Function.comp_def] using hτ.comp_of_eq hf rfl
  have hmap : ContinuousAt (fun q : ℝ × E => (τ q.1, q.2)) (0, x) :=
    ht.prodMk continuousAt_snd
  have hp : Tendsto (fun q : ℝ × E => Hp (τ q.1, q.2)) (𝓝 (0, x)) (𝓝 (Hp (0, x))) := by
    apply hHp.tendsto.comp
    simpa only [hτ0] using hmap.tendsto
  have hm : Tendsto (fun q : ℝ × E => -Hm (τ q.1, q.2)) (𝓝 (0, x)) (𝓝 (Hp (0, x))) := by
    have ht : Tendsto (fun q : ℝ × E => Hm (τ q.1, q.2)) (𝓝 (0, x)) (𝓝 (Hm (0, x))) := by
      apply hHm.tendsto.comp
      simpa only [hτ0] using hmap.tendsto
    simpa only [hmatch] using ht.neg
  have hH0 : H (0, x) = Hp (0, x) := by simp only [H, le_refl, ite_true, hτ0]
  have hH : ContinuousAt H (0, x) := by
    change Tendsto H (𝓝 (0, x)) (𝓝 (H (0, x)))
    rw [hH0]
    exact hp.if' hm
  have heq : signedFactoredMap Hp Hm τ = (fun q : ℝ × E => q.2 + q.1 • H q) := by
    funext q
    dsimp [signedFactoredMap, H]
    split_ifs with hq
    · rfl
    · rw [abs_of_neg (lt_of_not_ge hq), neg_smul, smul_neg]
  rw [heq]
  simpa only [hH0] using factoredParameter_hasFDerivAt_zero H x hH

end RothschildStein.G1

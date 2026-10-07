-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroCompactLpGeometry
public import RothschildStein.H3.FundamentalControlNorm
public import RothschildStein.H3.FundamentalSecondTypeZero

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- All second fundamental kernels have one common actual global
PV Lp bound on compact C1 sources, constructed from exact control geometry. -/
theorem exists_fundamental_second_compact_Lp_bounds_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    {p : ℝ} (hp : 1 < p) :
    ∃ M : ℝ, 0 < M ∧ ∀ i j : Fin q, ∀ f : (Fin N → ℝ) → ℝ,
      ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (H1.principalValueConvolution G C.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) volume := by
  classical
  obtain ⟨B, hB, hb⟩ := exists_typeZero_compact_Lp_bound_of_controlNorm G C
    (fun i => (H.fields_smooth G i).continuous.continuousOn) H.homogeneous hp
  have hk (i j : Fin q) : TypeZero G C.norm
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) :=
    fundamental_second_typeZero G (standingWithNorm G H C.norm)
      (fundamentalKernelWithNorm G H C.norm K) i j
  let b := fun i j : Fin q => kernelDerivativeBound C.norm
    (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) 1 * B
  have hbn (i j : Fin q) : 0 ≤ b i j :=
    mul_nonneg (kernelDerivativeBound_properties C.norm.gauge (hk i j).smooth 1).1 hB.le
  let M := 1 + ∑ i : Fin q, ∑ j : Fin q, b i j
  have hsum : 0 ≤ ∑ i : Fin q, ∑ j : Fin q, b i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hbn i j))
  refine ⟨M, by dsimp only [M]; linarith, ?_⟩
  intro i j f hf hs
  have hij : b i j ≤ M := by
    have h := (Finset.single_le_sum (fun j _ => hbn i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hbn i j)) (Finset.mem_univ i))
    dsimp only [M]
    linarith
  exact (hb _ (hk i j) f hf hs).2.trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hij) le_rfl)

end RothschildStein.H3

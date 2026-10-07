-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SumSquaresConvolutionTransfer
public import RothschildStein.H3.IntrinsicOperatorMollification
public import RothschildStein.H3.MollifierConvolutionLimit
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace RothschildStein.H3

/-- far part. The actual intrinsic order-two source transfers
to the right sum-of-squares on a globally smooth kernel. Mollification
proves the identity for compact continuous intrinsic jets, without any
Euclidean smoothness assumption on the input (BB p. 383). -/
theorem intrinsic_sumSquares_convolution_transfer {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (φ : G2.GroupMollifier G H.norm) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = u)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I u (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    {T : (Fin N → ℝ) → ℝ} (hT : ContDiff ℝ (⊤ : ℕ∞) T) (x : Fin N → ℝ) :
    let F := fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y
    G2.groupConvolution G F T x =
      G2.groupConvolution G u
        (sumSquaresWithDrift (fun i => G2.rightField G (H.fields i 0)) T) x := by
  classical
  let F := fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i : Fin q) : wordWeight (driftWeight (q := q)) [i.succ, i.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hnil : wordWeight (driftWeight (q := q)) [] ≤ 2 := by simp [wordWeight]
  have hu : Continuous u := hzero ▸ hc [] hnil
  have hsu : HasCompactSupport u := hzero ▸ hs [] hnil
  have hF : Continuous F := (hc [0] hw0).add (continuous_finsetSum _ (fun i _ => hc _ (hw2 i)))
  have hsF : HasCompactSupport F := by
    have hh := (hs [0] hw0).add (HasCompactSupport.finset_sum (fun i (_ : i ∈ Finset.univ) => hs _ (hw2 i)))
    have he : (jet [0] + ∑ i : Fin q, jet [i.succ, i.succ]) = F := by
      funext y
      simp only [F, Pi.add_apply, Finset.sum_apply]
    exact he ▸ hh
  have hsource (ε : ℝ) (he : 0 < ε) :
      sumSquaresWithDrift H.fields (G2.groupRegularize G φ u ε) = G2.groupRegularize G φ F ε :=
    sumSquaresWithDrift_groupRegularize_of_intrinsic_jets G H.fields (H.fields_smooth G)
      H.invariant φ u jet hzero hi hc hs he
  let Yr := fun i : Fin (q + 1) => G2.rightField G (H.fields i 0)
  let RT := sumSquaresWithDrift Yr T
  have hword (I : List (Fin (q + 1))) : Continuous (wordDerivative Yr I T) :=
    (contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ Yr
      (fun i => (G2.contDiff_rightField G (H.fields i 0)).contDiffOn) I T hT.contDiffOn)).continuous
  have hRT : Continuous RT := by
    change Continuous (fun y => wordDerivative Yr [0] T y +
      ∑ i : Fin q, wordDerivative Yr [i.succ, i.succ] T y)
    exact (hword [0]).add (continuous_finsetSum _ (fun i _ => hword [i.succ, i.succ]))
  have hleft := tendsto_groupConvolution_groupRegularize G φ hF hsF hT.continuous.locallyIntegrable x
  have hright := tendsto_groupConvolution_groupRegularize G φ hu hsu hRT.locallyIntegrable x
  have heq : (fun ε => G2.groupConvolution G (G2.groupRegularize G φ F ε) T x) =ᶠ[𝓝[>] 0]
      fun ε => G2.groupConvolution G (G2.groupRegularize G φ u ε) RT x := by
    filter_upwards [self_mem_nhdsWithin] with ε he
    obtain ⟨hsm, hcompact⟩ := G2.contDiff_hasCompactSupport_groupRegularize G φ he
      (p := (1 : ℝ≥0∞)) le_rfl (hu.memLp_of_hasCompactSupport hsu) hsu
    have hh := sumSquaresWithDrift_invariant_convolution_transfer G H.fields H.invariant
      hsm hcompact hT x
    rw [hsource ε he] at hh
    exact hh
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

end RothschildStein.H3

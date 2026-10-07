-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicOperatorMollification
public import RothschildStein.H3.MollifierConvolutionLimit
public import RothschildStein.H1.KernelPotential
public import RothschildStein.H1.FundamentalFirstDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace RothschildStein.H3

/-- (b) Pointwise representation of a compact intrinsic
order-two input and its horizontal first jets by the actual fundamental
kernel. The source is its drift jet plus diagonal second jets, so no
Euclidean differentiability of the input is imposed (BB Prop 8.49, p. 379). -/
theorem positive_representation_of_compact_intrinsic_jets {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (φ : G2.GroupMollifier G H.norm) (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I f (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I)) :
    let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
    f = G2.groupConvolution G F K ∧
      ∀ i : Fin q, jet [i.succ] =
        G2.groupConvolution G F (fieldDerivative (H.fields i.succ) K) := by
  classical
  let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw1 (i : Fin q) : wordWeight (driftWeight (q := q)) [i.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hw2 (i : Fin q) : wordWeight (driftWeight (q := q)) [i.succ, i.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hnil : wordWeight (driftWeight (q := q)) [] ≤ 2 := by simp [wordWeight]
  have hf : Continuous f := hzero ▸ hc [] hnil
  have hsf : HasCompactSupport f := hzero ▸ hs [] hnil
  have hF : Continuous F := (hc [0] hw0).add (continuous_finsetSum _ (fun i _ => hc _ (hw2 i)))
  have hsF : HasCompactSupport F := by
    have hh := (hs [0] hw0).add (HasCompactSupport.finset_sum (fun i (_ : i ∈ Finset.univ) => hs _ (hw2 i)))
    have he : (jet [0] + ∑ i : Fin q, jet [i.succ, i.succ]) = F := by
      funext x
      simp only [F, Pi.add_apply, Finset.sum_apply]
    exact he ▸ hh
  have hsource (ε : ℝ) (he : 0 < ε) :
      sumSquaresWithDrift H.fields (G2.groupRegularize G φ f ε) = G2.groupRegularize G φ F ε :=
    sumSquaresWithDrift_groupRegularize_of_intrinsic_jets G H.fields (H.fields_smooth G)
      H.invariant φ f jet hzero hi hc hs he
  have happrox (ε : ℝ) (he : 0 < ε) :=
    G2.contDiff_hasCompactSupport_groupRegularize G φ he (p := (1 : ℝ≥0∞)) le_rfl
      (hf.memLp_of_hasCompactSupport hsf) hsf
  constructor
  · funext x
    have hlim := (G2.tendstoUniformly_groupRegularize G φ hf hsf).tendsto_at x
    have hconv := tendsto_groupConvolution_groupRegularize G φ hF hsF K.locallyIntegrable x
    have heq : (fun ε => G2.groupConvolution G (G2.groupRegularize G φ F ε) K x) =ᶠ[𝓝[>] 0]
        fun ε => G2.groupRegularize G φ f ε x := by
      filter_upwards [self_mem_nhdsWithin] with ε he
      obtain ⟨hsm, hcomp⟩ := happrox ε he
      have hr := H.fundamental_twoSidedInverse G hQ K.locallyIntegrable K.smooth_off_zero
        K.homogeneous K.fundamental hsm hcomp x
      rw [← hsource ε he, G2.groupConvolution_eq_integral]
      convert hr using 1
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => mul_comm _ _
    exact tendsto_nhds_unique hlim (hconv.congr' heq)
  · intro i
    funext x
    have hlim := (tendstoUniformly_groupRegularize_of_weight_two_jets G H.fields
      (H.fields_smooth G) H.invariant φ f jet hzero hi hc hs [i.succ] (hw1 i)).tendsto_at x
    have hKi := H.horizontalKernel_locallyIntegrable G i (K.smooth_off_zero.of_le (by simp))
      K.homogeneous (by linarith)
    have hconv := tendsto_groupConvolution_groupRegularize G φ hF hsF hKi x
    have heq : (fun ε => G2.groupConvolution G (G2.groupRegularize G φ F ε)
        (fieldDerivative (H.fields i.succ) K) x) =ᶠ[𝓝[>] 0]
        fun ε => wordDerivative H.fields [i.succ] (G2.groupRegularize G φ f ε) x := by
      filter_upwards [self_mem_nhdsWithin] with ε he
      obtain ⟨hsm, hcomp⟩ := happrox ε he
      have hr := congrFun (K.firstDerivative_representation G H hQ i hsm hcomp) x
      rw [hsource ε he] at hr
      exact hr.symm
    exact tendsto_nhds_unique hlim (hconv.congr' heq)

end RothschildStein.H3

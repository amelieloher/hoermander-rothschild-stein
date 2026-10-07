-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PositiveRepresentation
public import RothschildStein.H3.FundamentalCorrectionCoefficients
public import RothschildStein.H3.MollifierPrincipalValueLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace RothschildStein.H3

/-- Pointwise second-jet representation with a fixed correction family
for the fundamental kernel. The source has a global Hölder bound
(BB Proposition 8.49, p. 379). -/
theorem second_representation_with_fixed_coefficients {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (hsym : H.norm.Symmetric) (φ : G2.GroupMollifier G H.norm)
    (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I f (jet I))
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    {α A : ℝ} (hα : 0 < α)
    (hholder : ∀ x y,
      |(jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) -
        (jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y)| ≤
        A * G2.gaugeDistance G H.norm x y ^ α) :
    let c := fundamentalCorrectionCoefficients G H K hQ
      let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
      ∀ i j : Fin q, jet [i.succ, j.succ] = fun x =>
        H1.principalValueConvolution G H.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F x +
          c i j * F x := by
  classical
  let c := fundamentalCorrectionCoefficients G H K hQ
  let F := fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i j : Fin q) : wordWeight (driftWeight (q := q)) [i.succ, j.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have hnil : wordWeight (driftWeight (q := q)) [] ≤ 2 := by simp [wordWeight]
  have hf : Continuous f := hzero ▸ hc [] hnil
  have hsf : HasCompactSupport f := hzero ▸ hs [] hnil
  have hF : Continuous F := (hc [0] hw0).add (continuous_finsetSum _ (fun i _ => hc _ (hw2 i i)))
  have hsF : HasCompactSupport F := by
    have hh := (hs [0] hw0).add
      (HasCompactSupport.finset_sum (fun i (_ : i ∈ Finset.univ) => hs _ (hw2 i i)))
    have he : (jet [0] + ∑ i : Fin q, jet [i.succ, i.succ]) = F := by
      funext x
      simp only [F, Pi.add_apply, Finset.sum_apply]
    exact he ▸ hh
  have htype := (Classical.choose_spec (convolution_formulas_of_fundamental_kernel G H K hQ)).1
  have hrep := (Classical.choose_spec (convolution_formulas_of_fundamental_kernel G H K hQ)).2
  dsimp only
  intro i j
  funext x
  have hlim := (tendstoUniformly_groupRegularize_of_weight_two_jets G H.fields
    (H.fields_smooth G) H.invariant φ f jet hzero hi hc hs
    [i.succ, j.succ] (hw2 i j)).tendsto_at x
  have hpv := tendsto_principalValueConvolution_groupRegularize G H.norm hsym φ
    (htype i j) hF hsF hα hholder x
  have hsource := G2.tendstoUniformly_groupRegularize G φ hF hsF
  have hright := hpv.add ((hsource.tendsto_at x).const_mul (c i j))
  have heq : (fun ε => H1.principalValueConvolution G H.norm
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
      (G2.groupRegularize G φ F ε) x + c i j * G2.groupRegularize G φ F ε x) =ᶠ[𝓝[>] 0]
      fun ε => wordDerivative H.fields [i.succ, j.succ] (G2.groupRegularize G φ f ε) x := by
    filter_upwards [self_mem_nhdsWithin] with ε he
    obtain ⟨hsm, hcomp⟩ := G2.contDiff_hasCompactSupport_groupRegularize G φ he
      (p := (1 : ℝ≥0∞)) le_rfl (hf.memLp_of_hasCompactSupport hsf) hsf
    have hr := congrFun ((hrep _ hsm hcomp).2.2.2.2.2.2.2 i j) x
    rw [sumSquaresWithDrift_groupRegularize_of_intrinsic_jets G H.fields
      (H.fields_smooth G) H.invariant φ f jet hzero hi hc hs he] at hr
    exact hr.symm
  exact tendsto_nhds_unique hlim (hright.congr' heq)

end RothschildStein.H3

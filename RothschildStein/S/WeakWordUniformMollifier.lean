-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ZeroExtendedCommutatorRepresentation
public import RothschildStein.S.KernelUniformConvergenceLocal
public import RothschildStein.S.MollifierUniformLocal
public import RothschildStein.S.UniformListSums

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- Classical words of ordinary zero-extended mollification
converge uniformly on an interior compact patch to continuous weak
word representatives. Local coefficients are replaced by germs only
on a fixed compact tube; no global input integrability is required
(BB Thm 2.20 and Lemma 2.21, pp. 86–87). -/
theorem tendstoUniformlyOn_weakWord_mollifier_of_coefficient_germs
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j,ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (B : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hB : ∀ j,ContDiff ℝ (⊤ : ℕ∞) (B j))
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ : ℝ} (hd : 0 < δ) (hδ : cthickening δ (closure U) ⊆ Ω)
    (hG : ∀ j z,z ∈ cthickening δ (closure U) → B j =ᶠ[𝓝 z] X j)
    (I : List (Fin q)) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hw : ∀ J,J.Sublist I → hasWeakWordDeriv X Ω J f (jet J))
    (hct : ∀ J,J.Sublist I → ContinuousOn (jet J) (Ω : Set (Fin n → ℝ))) :
    TendstoUniformlyOn (fun ε : ℝ => wordDerivative X I
      (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε))
      (jet I) (𝓝[>] 0) U := by
  let pairs := smoothFriedrichsCommutatorPairs B hB I
  have ht : ∀ r ∈ pairs,TendstoUniformlyOn
      (fun ε : ℝ => friedrichsKernelOp r.1.family (jet r.2) ε)
      (fun _ => 0) (𝓝[>] 0) U := by
    intro r hr
    have hs := (friedrichsCommutatorPairs_subword _ _ I hr).1
    exact tendstoUniformlyOn_friedrichsKernelOp_zero_of_compact
      (r.1.toBounded U hc δ) hd
      (smoothFriedrichsCommutatorPairs_hasVanishingMean B hB I hr U hc δ)
      hc.cthickening ((hct r.2 hs).mono hδ) (subset_interior_cthickening hd)
      (fun ε hε x hx y hy => add_smul_mem_interior_cthickening hε hx hy)
  have hterr := tendstoUniformlyOn_listSum_zero pairs
    (fun r ε => friedrichsKernelOp r.1.family (jet r.2) ε) ht
  have hcl : closure U ⊆ Ω := by
    intro x hx
    apply hδ
    exact mem_cthickening_of_dist_le x x δ (closure U) hx (by simpa only [dist_self] using hd.le)
  have htbase := tendstoUniformlyOn_regularize_zeroExtension_local Ω hc hcl
    (hct I (List.Sublist.refl I))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [Ioo_mem_nhdsGT hd,
    Metric.tendstoUniformlyOn_iff.mp hterr (η/2) (half_pos hη),
    Metric.tendstoUniformlyOn_iff.mp htbase (η/2) (half_pos hη)] with ε hε he hb
  intro x hx
  have hn : ‖(pairs.map (fun r => friedrichsKernelOp r.1.family (jet r.2) ε x)).sum‖ < η/2 := by
    simpa only [dist_zero_left] using he x hx
  have hm : ‖euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator (jet I)) ε x-jet I x‖ < η/2 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hb x hx
  have hr := zeroExtended_commutator_representation Ω X hX B hB hU hc hε hδ hG I f jet hzero hw hx
  have heq : wordDerivative X I (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε) x-jet I x =
      (pairs.map (fun r => friedrichsKernelOp r.1.family (jet r.2) ε x)).sum +
      (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator (jet I)) ε x-jet I x) := by
    dsimp [pairs]
    linarith
  rw [dist_eq_norm,norm_sub_rev,heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

end RothschildStein.S

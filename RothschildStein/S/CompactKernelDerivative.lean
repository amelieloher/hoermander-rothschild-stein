-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactKernelIntegral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A directional derivative passes under integration against
locally integrable data when the joint smooth kernel has one common compact
integration support (BB pp. 76–78; weak transfer). -/
theorem fderiv_compactKernelIntegral_apply {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {k : P → (Fin n → ℝ) → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry k))
    (hks : ∀ x z, z ∉ K → k x z = 0) {h : (Fin n → ℝ) → ℝ}
    (hh : LocallyIntegrable h volume) (x v : P) :
    fderiv ℝ (fun x => ∫ z, h z * k x z) x v =
      ∫ z, h z * fderiv ℝ (uncurry k) (x,z) (v,0) := by
  let g : P → (Fin n → ℝ) → ℝ := fun x z => k x (-z)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (uncurry g) :=
    hk.comp (contDiff_fst.prodMk contDiff_snd.neg)
  have hgs : ∀ x z, x ∈ (univ : Set P) → z ∉ -K → g x z = 0 :=
    fun x z _ hz => hks x (-z) hz
  have hdz : ∀ z ∉ -K, fderiv ℝ (uncurry g) (x,z) = 0 := by
    intro z hz
    apply (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
    have H := (continuous_snd.tendsto (x,z)).eventually
      (hK.neg.isClosed.isOpen_compl.mem_nhds hz)
    filter_upwards [H] with p hp
    exact hgs p.1 p.2 (mem_univ _) hp
  have hcd : HasCompactSupport (fun z => fderiv ℝ (uncurry g) (x,z)) := by
    apply hK.neg.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.neg.isClosed
    intro z hz
    by_contra hn
    exact hz (hdz z hn)
  have hdcont : Continuous (fun z => fderiv ℝ (uncurry g) (x,z)) :=
    (hg.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)).continuous.comp
      (continuous_const.prodMk continuous_id)
  let L : P →L[ℝ] P × (Fin n → ℝ) := (ContinuousLinearMap.id ℝ P).prod 0
  let A := convolution h (fun z => fderiv ℝ (uncurry g) (x,z))
    ((ContinuousLinearMap.mul ℝ ℝ).precompR (P × (Fin n → ℝ))) volume 0
  have H := hasFDerivAt_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℝ)
    isOpen_univ hK.neg hgs hh (hg.of_le (by simp)).contDiffOn
    (x,(0 : Fin n → ℝ)) (mem_univ _)
  have hd : HasFDerivAt (fun x => ∫ z, h z * k x z) (A.comp L) x := by
    convert H.comp x L.hasFDerivAt using 1
    · ext a
      change (∫ z, h z * k a z) = ∫ z, h z * k a (-(0-z))
      simp only [zero_sub,neg_neg]
    · rfl
  rw [hd.fderiv,ContinuousLinearMap.comp_apply]
  change A (v,0) = _
  rw [show A = convolution h (fun z => fderiv ℝ (uncurry g) (x,z))
    ((ContinuousLinearMap.mul ℝ ℝ).precompR (P × (Fin n → ℝ))) volume 0 from rfl]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hh hcd hdcont]
  change (∫ z, h z * fderiv ℝ (uncurry g) (x,0-z) (v,0)) = _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  change h z * fderiv ℝ (uncurry g) (x,0-z) (v,0) =
    h z * fderiv ℝ (uncurry k) (x,z) (v,0)
  rw [zero_sub]
  congr 1
  let N : P × (Fin n → ℝ) →L[ℝ] P × (Fin n → ℝ) :=
    (ContinuousLinearMap.fst ℝ P (Fin n → ℝ)).prod
      (-(ContinuousLinearMap.snd ℝ P (Fin n → ℝ)))
  have hc := (hk.differentiable (by simp)).differentiableAt.hasFDerivAt.comp (x,-z) N.hasFDerivAt
  have he : uncurry k ∘ N = uncurry g := rfl
  rw [he] at hc
  rw [hc.fderiv]
  simp [N,ContinuousLinearMap.comp_apply]

end RothschildStein.S

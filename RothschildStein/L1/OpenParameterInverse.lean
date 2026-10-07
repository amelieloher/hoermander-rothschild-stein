-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.BlockDerivativeEquiv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1

/-- A smooth map on an open domain has a parameter inverse smooth
on one open neighborhood. This uses smoothness throughout the original
domain, not just infinite differentiability at its center. -/
theorem exists_open_parameter_inverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Φ : (E × E) → E) {O : Set (E × E)} (hO : IsOpen O)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O) (p : E × E) (hp : p ∈ O)
    (A : E →L[ℝ] E) (B : E ≃L[ℝ] E)
    (hd : HasFDerivAt Φ (A.coprod (B : E →L[ℝ] E)) p) :
    ∃ W : Set (E × E), IsOpen W ∧ (p.1,Φ p) ∈ W ∧
      ∃ Θ : (E × E) → E, ContDiffOn ℝ (⊤ : ℕ∞) Θ W ∧
        Θ (p.1,Φ p) = p.2 ∧ (∀ q ∈ W, Φ (q.1,Θ q) = q.2) ∧
        (∀ᶠ v in 𝓝 p, Θ (v.1,Φ v) = v.2) := by
  let F : (E × E) → (E × E) := fun q => (q.1,Φ q)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F O := contDiffOn_fst.prodMk hΦ
  have hFa : ContDiffAt ℝ (⊤ : ℕ∞) F p := hF.contDiffAt (hO.mem_nhds hp)
  let L := blockDerivativeEquiv A B
  have hD : HasFDerivAt F (L : (E × E) →L[ℝ] (E × E)) p := by
    rw [blockDerivativeEquiv_toCLM]
    exact hasFDerivAt_fst.prodMk hd
  have hn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let e := hFa.toOpenPartialHomeomorph F hD hn
  have he : (e : (E × E) → (E × E)) = F := rfl
  have hpS : p ∈ e.source := hFa.mem_toOpenPartialHomeomorph_source hD hn
  have hpT : F p ∈ e.target := hFa.image_mem_toOpenPartialHomeomorph_target hD hn
  have hInv : e.symm (F p) = p := e.left_inv hpS
  have hder : {q : E × E | ∃ M : (E × E) ≃L[ℝ] (E × E),
      (M : (E × E) →L[ℝ] (E × E)) = fderiv ℝ F q} ∈ 𝓝 p := by
    have hc := hFa.continuousAt_fderiv hn
    have hL := L.nhds
    rw [← hD.fderiv] at hL
    exact hc.preimage_mem_nhds hL
  obtain ⟨V,hVsub,hVopen,hpV⟩ := mem_nhds_iff.mp (inter_mem (hO.mem_nhds hp) hder)
  let W := e.target ∩ e.symm ⁻¹' V
  have hW : IsOpen W := e.isOpen_inter_preimage_symm hVopen
  have hpW : F p ∈ W := ⟨hpT,by
    change e.symm (F p) ∈ V
    rwa [hInv]⟩
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) e.symm W := by
    intro q hq
    have hv := hVsub hq.2
    obtain ⟨M,hM⟩ := hv.2
    have hc := hF.contDiffAt (hO.mem_nhds hv.1)
    have hdq : HasFDerivAt e (M : (E × E) →L[ℝ] (E × E)) (e.symm q) := by
      rw [he,hM]
      exact (hc.differentiableAt hn).hasFDerivAt
    exact (e.contDiffAt_symm hq.1 hdq (by simpa only [he] using hc)).contDiffWithinAt
  refine ⟨W,hW,hpW,fun q => (e.symm q).2,hs.snd,?_,?_,?_⟩
  · exact congrArg Prod.snd hInv
  · intro q hq
    have hh := e.right_inv hq.1
    rw [he] at hh
    have hf := congrArg (Prod.fst : E × E → E) hh
    change (e.symm q).1 = q.1 at hf
    have hg := congrArg (Prod.snd : E × E → E) hh
    change Φ ((e.symm q).1,(e.symm q).2) = q.2 at hg
    rwa [hf] at hg
  · filter_upwards [e.open_source.mem_nhds hpS] with v hv
    exact congrArg Prod.snd (e.left_inv hv)
end RothschildStein.L1

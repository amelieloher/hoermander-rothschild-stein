-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakKernelTransferGermPatch
public import RothschildStein.S.SmoothCommutatorPairs
public import RothschildStein.S.FieldDerivativeListSum
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- With global coefficient germs on the interior tube, the recursive
kernel list represents every original local classical word
of the mollified function in terms of its weak subword derivatives.
The proof uses weak transfer and induction on ordinary word length
(BB (2.9)–(2.12), pp. 77–79). -/
theorem smoothFriedrichsCommutatorPairs_representation_of_coefficient_germs
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (B : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hB : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (B j))
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ ε : ℝ} (hε : ε ∈ Ioo 0 δ) (hδ : cthickening δ (closure U) ⊆ Ω)
    (hG : ∀ j z, z ∈ cthickening δ (closure U) → B j =ᶠ[𝓝 z] X j)
    (I : List (Fin q)) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hw : ∀ J, J.Sublist I → hasWeakWordDeriv X Ω J f (jet J))
    {x : Fin n → ℝ} (hx : x ∈ U) :
    wordDerivative X I (friedrichsKernelOp (smoothBaseFriedrichsKernel n).family f ε) x =
      friedrichsKernelOp (smoothBaseFriedrichsKernel n).family (jet I) ε x +
      ((smoothFriedrichsCommutatorPairs B hB I).map
        (fun p => friedrichsKernelOp p.1.family (jet p.2) ε x)).sum := by
  induction I generalizing x with
  | nil => simp only [wordDerivative,smoothFriedrichsCommutatorPairs,
      friedrichsCommutatorPairs,List.map_nil,List.sum_nil,add_zero,hzero]
  | cons j I ih =>
    let pairs := smoothFriedrichsCommutatorPairs B hB I
    have hsI : I.Sublist (j::I) := (List.Sublist.refl I).cons j
    have hs (p : SmoothFriedrichsKernel n × List (Fin q)) (hp : p ∈ pairs) :
        p.2.Sublist I :=
      (friedrichsCommutatorPairs_subword _ _ I hp).1
    have hd (K : SmoothFriedrichsKernel n) (J : List (Fin q))
        (hJ : J.Sublist (j::I)) :
        DifferentiableAt ℝ (friedrichsKernelOp K.family (jet J) ε) x :=
      (((contDiffOn_friedrichsKernelOp_interior_patch Ω K hU hc hε.1 hε.2 hδ
        (hw J hJ).2.1).differentiableOn (by simp)) x hx).differentiableAt (hU.mem_nhds hx)
    have ht : ∀ p ∈ pairs,
        DifferentiableAt ℝ (friedrichsKernelOp p.1.family (jet p.2) ε) x :=
      fun p hp => hd p.1 p.2 ((hs p hp).trans hsI)
    have he : wordDerivative X I (friedrichsKernelOp (smoothBaseFriedrichsKernel n).family f ε) =ᶠ[𝓝 x]
        (fun a => friedrichsKernelOp (smoothBaseFriedrichsKernel n).family (jet I) ε a +
          (pairs.map (fun p => friedrichsKernelOp p.1.family (jet p.2) ε a)).sum) := by
      filter_upwards [hU.mem_nhds hx] with a ha
      exact ih (fun J hJ => hw J (hJ.trans hsI)) ha
    have hgI := (hasWeakWordDeriv_cons_iff X Ω hX
      (hw I hsI) j).mp (hw (j::I) (List.Sublist.refl _))
    have hmap : (pairs.map (fun p => fieldDerivative (X j)
        (friedrichsKernelOp p.1.family (jet p.2) ε) x)) =
        pairs.map (fun p => friedrichsKernelOp p.1.family (jet (j::p.2)) ε x +
          friedrichsKernelOp (smoothKernelTransfer p.1 (B j) (hB j)).family (jet p.2) ε x) := by
      apply List.map_congr_left
      intro p hp
      have hgp := (hasWeakWordDeriv_cons_iff X Ω hX
        (hw p.2 ((hs p hp).trans hsI)) j).mp
          (hw (j::p.2) ((hs p hp).cons_cons j))
      exact weak_friedrichsKernel_transfer_germ_patch Ω p.1 X j (B j) (hB j) hgp hε hδ (hG j) hx
    rw [wordDerivative]
    unfold fieldDerivative
    rw [he.fderiv_eq,fderiv_fun_add (hd (smoothBaseFriedrichsKernel n) I hsI)
      (differentiableAt_listSum pairs _ x ht)]
    change fieldDerivative (X j)
      (friedrichsKernelOp (smoothBaseFriedrichsKernel n).family (jet I) ε) x +
      fieldDerivative (X j) (fun a => (pairs.map
        (fun p => friedrichsKernelOp p.1.family (jet p.2) ε a)).sum) x = _
    rw [weak_friedrichsKernel_transfer_germ_patch Ω (smoothBaseFriedrichsKernel n)
      X j (B j) (hB j) hgI hε hδ (hG j) hx,fieldDerivative_listSum (X j) pairs _ x ht,hmap]
    simp only [smoothFriedrichsCommutatorPairs,friedrichsCommutatorPairs,
      List.map_append,List.map_map,List.sum_append,List.map_singleton,List.sum_singleton]
    rw [List.sum_map_add]
    dsimp only [pairs,smoothFriedrichsCommutatorPairs,Function.comp_def]
    ring

end RothschildStein.S

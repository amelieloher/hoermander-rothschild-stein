-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.PatchChoice
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.Distribution

/-- compatible complex smooth functions on an open cover
glue smoothly, reusing the existing real patch-choice implementation. -/
theorem exists_complex_smooth_gluing {N : ℕ} {ι : Type*}
    (Ω : Set (Fin N → ℝ)) (hΩ : IsOpen Ω)
    (U : ι → Set (Fin N → ℝ)) (f : ι → (Fin N → ℝ) → ℂ)
    (hUopen : ∀ i, IsOpen (U i)) (hUsub : ∀ i, U i ⊆ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i)
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (f i) (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ F : (Fin N → ℝ) → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F Ω ∧
      ∀ i, EqOn F (f i) (U i) := by
  classical
  have hpart (L : ℂ →L[ℝ] ℝ) :
      ContDiffOn ℝ (⊤ : ℕ∞) (Hormander.F.patchChoice Ω U (fun i x => L (f i x)) hcover) Ω ∧
      ∀ i, EqOn (Hormander.F.patchChoice Ω U (fun i x => L (f i x)) hcover)
        (fun x => L (f i x)) (U i) := by
    let p := Hormander.F.patchChoice Ω U (fun i x => L (f i x)) hcover
    have he (i : ι) : EqOn p (fun x => L (f i x)) (U i) := by
      intro x hx
      have hxΩ := hUsub i hx
      have hj := Classical.choose_spec (hcover x hxΩ)
      change (if h : x ∈ Ω then L (f (Classical.choose (hcover x h)) x) else 0) = _
      rw [dite_eq_left hxΩ]
      exact congrArg L (hcompat (Classical.choose (hcover x hxΩ)) i ⟨hj, hx⟩)
    have hae (i : ι) : (fun x => L (f i x)) =ᵐ[volume.restrict (U i)] p :=
      (ae_restrict_iff' (hUopen i).measurableSet).mpr
        (Eventually.of_forall (fun x hx => (he i hx).symm))
    have hL : ContDiff ℝ (⊤ : ℕ∞) (fun z => L z) := L.contDiff
    have hp := Hormander.F.patch_choice_smoothness hΩ U (fun i x => L (f i x)) p
      hUopen hUsub hcover (fun i => hL.comp_contDiffOn (hf i)) hae
    exact ⟨hp.1, he⟩
  obtain ⟨hr, her⟩ := hpart Complex.reCLM
  obtain ⟨hi, hei⟩ := hpart Complex.imCLM
  let R := Hormander.F.patchChoice Ω U (fun i x => (f i x).re) hcover
  let I := Hormander.F.patchChoice Ω U (fun i x => (f i x).im) hcover
  refine ⟨fun x => (R x : ℂ) + Complex.I * (I x : ℂ), ?_, ?_⟩
  · have hC : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    exact (hC.comp_contDiffOn hr).add
      (contDiffOn_const.mul (hC.comp_contDiffOn hi))
  · intro i x hx
    change (R x : ℂ) + Complex.I * (I x : ℂ) = f i x
    rw [show R x = (f i x).re from her i hx, show I x = (f i x).im from hei i hx]
    simpa only [mul_comm Complex.I] using Complex.re_add_im (f i x)

end RothschildStein.Distribution

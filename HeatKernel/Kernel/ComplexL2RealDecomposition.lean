-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Complex.Basic

/-! # Real and imaginary decomposition through an L² real embedding

The scalar real representative formula identifies the images of the real and
imaginary parts of every complex L² class. It supplies the spanning property
used to identify complex operators from their action on real functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- A real embedding with its scalar representative formula spans complex L² by real and imaginary parts. -/
theorem exists_real_imaginary_L2_decomposition {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (j : Lp ℝ 2 μ → Lp ℂ 2 μ)
    (hj : ∀ f, j f =ᵐ[μ] fun x => (f x : ℂ)) (z : Lp ℂ 2 μ) :
    ∃ a b, z = j a + Complex.I • j b := by
  let a : Lp ℝ 2 μ := Complex.reCLM.compLp z
  let b : Lp ℝ 2 μ := Complex.imCLM.compLp z
  refine ⟨a, b, ?_⟩
  apply Lp.ext
  filter_upwards [hj a, hj b, Complex.reCLM.coeFn_compLp z, Complex.imCLM.coeFn_compLp z,
    Lp.coeFn_add (j a) (Complex.I • j b), Lp.coeFn_smul Complex.I (j b)]
    with x hja hjb ha hb hadd hsmul
  change a x = (z x).re at ha
  change b x = (z x).im at hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsmul
  rw [hadd, hsmul, hja, hjb, ha, hb]
  simpa only [mul_comm] using (Complex.re_add_im (z x)).symm

end HeatKernel

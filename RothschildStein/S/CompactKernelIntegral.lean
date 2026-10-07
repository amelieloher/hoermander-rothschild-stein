-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
namespace RothschildStein.S
variable {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G}

/-- Integration of a smooth parameter kernel with one common compact
support against locally integrable data is smooth (BB pp. 75–78; differentiation
under the integral via Mathlib's parameter convolution theorem). -/
theorem contDiffOn_compactKernelIntegral {U : Set P} (hU : IsOpen U)
    {K : Set G} (hK : IsCompact K) {k : P → G → ℝ}
    (hks : ∀ x z, x ∈ U → z ∉ K → k x z = 0)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) (uncurry k) (U ×ˢ univ))
    {h : G → ℝ} (hh : LocallyIntegrable h μ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∫ z, h z * k x z ∂μ) U := by
  let g : P → G → ℝ := fun x z => k x (-z)
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun p : P × G => (p.1,-p.2)) :=
    contDiff_fst.prodMk contDiff_snd.neg
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (uncurry g) (U ×ˢ univ) :=
    hk.comp hneg.contDiffOn (fun p hp => ⟨hp.1,mem_univ _⟩)
  have hgs : ∀ x z, x ∈ U → z ∉ -K → g x z = 0 := by
    intro x z hx hz
    exact hks x (-z) hx hz
  have H := contDiffOn_convolution_right_with_param_comp (ContinuousLinearMap.mul ℝ ℝ)
    (contDiffOn_const (c := (0 : G))) hU hK.neg hgs hh hg
  convert H using 1
  ext x
  change (∫ z, h z * k x z ∂μ) = ∫ z, h z * k x (-(0-z)) ∂μ
  simp only [zero_sub,neg_neg]

end RothschildStein.S

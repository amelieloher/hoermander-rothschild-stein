-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelWeights
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A [0,1]-valued Lipschitz cutoff which vanishes outside U.
BB Definition 7.9, p. 299. -/
structure KernelCutoff (U : Set X) (L : ℝ≥0) (a : X → ℝ) : Prop where
  lipschitz : LipschitzWith L a
  nonneg : ∀ x, 0 ≤ a x
  le_one : ∀ x, a x ≤ 1
  outside : ∀ x, x ∉ U → a x = 0

/-- BB (7.5), p. 299: the cutoff product on U × U, zero elsewhere. -/
def localizedKernel (U : Set X) (a b : X → ℝ) (K : X → X → ℝ) (x y : X) : ℝ := by
  classical
  exact if x ∈ U ∧ y ∈ U then a x * K x y * b y else 0

/-- Measurability of the zero extension requires only measurability on U × U. -/
theorem measurable_localizedKernel {U : Set X} {a b : X → ℝ} {K : X → X → ℝ}
    {Lₐ Lᵦ : ℝ≥0} (hU : MeasurableSet U) (ha : KernelCutoff U Lₐ a)
    (hb : KernelCutoff U Lᵦ b) (hK : Measurable (fun p : U × U => K p.1 p.2)) :
    Measurable (fun p : X × X => localizedKernel U a b K p.1 p.2) := by
  classical
  apply measurable_of_restrict_of_restrict_compl (hU.prod hU)
  · let j : (U ×ˢ U) → U × U := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
    have hj : Measurable j := by
      exact (measurable_fst.comp measurable_subtype_coe).subtype_mk.prodMk
        ((measurable_snd.comp measurable_subtype_coe).subtype_mk)
    have hm := ((ha.lipschitz.continuous.measurable.comp
      (measurable_fst.comp measurable_subtype_coe)).mul (hK.comp hj)).mul
      (hb.lipschitz.continuous.measurable.comp (measurable_snd.comp measurable_subtype_coe))
    convert hm using 1
    funext p
    change (if p.1.1 ∈ U ∧ p.1.2 ∈ U then _ else _) = _
    have hp : p.1.1 ∈ U ∧ p.1.2 ∈ U := p.2
    rw [ite_eq_left hp]
    rfl
  · have he : (U ×ˢ U)ᶜ.domRestrict (fun p : X × X => localizedKernel U a b K p.1 p.2) =
        fun _ => 0 := by
      funext p
      exact ite_eq_right p.2
    rw [he]
    exact measurable_const

omit [BorelSpace X] in
/-- The size constant is preserved by localization. -/
theorem localizedKernel_size {μ : Measure X} {U : Set X} {β ν A S : ℝ}
    {a b : X → ℝ} {K : X → X → ℝ} {Lₐ Lᵦ : ℝ≥0}
    (ha : KernelCutoff U Lₐ a) (hb : KernelCutoff U Lᵦ b) (hK : KernelClass μ U β ν A S K)
    {x y : X} (hxy : x ≠ y) :
    |localizedKernel U a b K x y| ≤ A * kernelWeight μ ν x y := by
  classical
  unfold localizedKernel
  split_ifs with h
  · rw [abs_mul, abs_mul, abs_of_nonneg (ha.nonneg x), abs_of_nonneg (hb.nonneg y)]
    calc
      _ ≤ 1 * |K x y| * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_right (ha.le_one x) (abs_nonneg _)) (hb.le_one y)
        (hb.nonneg y) (by positivity)
      _ = |K x y| := by ring
      _ ≤ _ := hK.size x h.1 y h.2 hxy
  · simpa only [abs_zero] using mul_nonneg hK.A_nonneg (kernelWeight_nonneg μ ν x y)

end RothschildStein.H2

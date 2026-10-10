-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.TentLayers
import Mathlib.Tactic

/-! # Weighted energy bounds from small and large distance layers

The small layers use a fixed inner-ball estimate. The large layers use their
own oscillation estimate. Integration of the two ranges preserves the original
distance weight on the energy side.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Integrating separate inner-ball and outer-layer estimates gives a weighted estimate.
The two local oscillation estimates are explicit inputs. -/
theorem lintegral_weighted_le_of_layer_poincare {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d : α → ℝ} (hd : Measurable d)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k) {w f g : α → ℝ≥0∞}
    (hw : Measurable w) (hf : Measurable f) (hg : Measurable g)
    (hlayers : ∀ x, w x = ∫⁻ s in Ioo (0 : ℝ) 1, (Ioi (d x)).indicator k s)
    {a b C : ℝ≥0∞}
    (hweight : ∀ x, d x < 1 / 2 → 1 ≤ C * w x)
    (hsmall : ∀ s ∈ Ioo (0 : ℝ) (1 / 2),
      (∫⁻ x in {x | d x < s}, f x ∂μ) ≤ a * ∫⁻ x in {x | d x < 1 / 2}, g x ∂μ)
    (hlarge : ∀ s ∈ Ico (1 / 2 : ℝ) 1,
      (∫⁻ x in {x | d x < s}, f x ∂μ) ≤ b * ∫⁻ x in {x | d x < s}, g x ∂μ) :
    (∫⁻ x, w x * f x ∂μ) ≤
      ((∫⁻ s in Ioo (0 : ℝ) (1 / 2), k s) * a * C + b) * ∫⁻ x, w x * g x ∂μ := by
  let E := ∫⁻ x, w x * g x ∂μ
  have hinner : (∫⁻ x in {x | d x < 1 / 2}, g x ∂μ) ≤ C * E := by
    dsimp only [E]
    rw [← lintegral_indicator (measurableSet_lt hd measurable_const),
      ← lintegral_const_mul C (f := fun x => w x * g x) (hw.mul hg)]
    apply lintegral_mono
    intro x
    by_cases hx : d x < 1 / 2
    · rw [indicator_of_mem (show x ∈ {x | d x < 1 / 2} from hx)]
      simpa only [one_mul, mul_assoc] using mul_le_mul' (hweight x hx) (le_refl (g x))
    · rw [indicator_of_notMem (show x ∉ {x | d x < 1 / 2} from hx)]
      exact zero_le
  have hbg : Measurable (fun s : ℝ => ∫⁻ x in {x | d x < s}, g x ∂μ) := by
    have hm : Measurable (fun z : ℝ × α => if d z.2 < z.1 then g z.2 else 0) :=
      Measurable.ite (measurableSet_lt (hd.comp measurable_snd) measurable_fst)
        (hg.comp measurable_snd) measurable_const
    have hm' := hm.lintegral_prod_right' (ν := μ)
    convert hm' using 1
    funext s
    rw [← lintegral_indicator (measurableSet_lt hd measurable_const)]
    rfl
  have he := lintegral_mul_eq_lintegral_layers (μ := μ) hd hk hg hlayers
  have hsmall' :
      (∫⁻ s in Ioo (0 : ℝ) (1 / 2), k s * ∫⁻ x in {x | d x < s}, f x ∂μ) ≤
      (∫⁻ s in Ioo (0 : ℝ) (1 / 2), k s) * a * C * E := by
    calc
      _ ≤ ∫⁻ s in Ioo (0 : ℝ) (1 / 2), k s * (a * (C * E)) := by
        apply setLIntegral_mono (by fun_prop)
        intro s hs
        exact mul_le_mul' le_rfl ((hsmall s hs).trans (mul_le_mul' le_rfl hinner))
      _ = _ := by rw [lintegral_mul_const _ hk]; ring
  have hlarge' :
      (∫⁻ s in Ico (1 / 2 : ℝ) 1, k s * ∫⁻ x in {x | d x < s}, f x ∂μ) ≤ b * E := by
    calc
      _ ≤ ∫⁻ s in Ico (1 / 2 : ℝ) 1, b * (k s * ∫⁻ x in {x | d x < s}, g x ∂μ) := by
        apply setLIntegral_mono (by fun_prop)
        intro s hs
        calc
          _ ≤ k s * (b * ∫⁻ x in {x | d x < s}, g x ∂μ) :=
            mul_le_mul' le_rfl (hlarge s hs)
          _ = _ := by ring
      _ = b * ∫⁻ s in Ico (1 / 2 : ℝ) 1, k s * ∫⁻ x in {x | d x < s}, g x ∂μ :=
        lintegral_const_mul b (hk.mul hbg)
      _ ≤ b * ∫⁻ s in Ioo (0 : ℝ) 1, k s * ∫⁻ x in {x | d x < s}, g x ∂μ := by
        apply mul_le_mul' le_rfl
        apply lintegral_mono_set
        intro s hs
        exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs.1, hs.2⟩
      _ = b * E := by rw [← he]
  rw [lintegral_mul_eq_lintegral_layers (μ := μ) hd hk hf hlayers,
    ← Ioo_union_Ico_eq_Ioo (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1),
    lintegral_union measurableSet_Ico (by
      apply Set.disjoint_left.mpr
      intro s hs ht
      exact (not_lt_of_ge ht.1) hs.2)]
  exact (add_le_add hsmall' hlarge').trans_eq (by dsimp only [E]; ring)

end HeatKernel.Sobolev

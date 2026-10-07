-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

omit [MetricSpace X] [MetricSpace Y] in
/-- A surjective change of variables preserves the supremum
on the exact inverse-image domain, including an empty domain (BB p. 339). -/
theorem holderSup_surjective_pullback (φ : X → Y) (hφ : Function.Surjective φ)
    (A : Set Y) (f : Y → ℝ) :
    H2.holderSup (φ ⁻¹' A) (f ∘ φ) = H2.holderSup A f := by
  unfold H2.holderSup
  apply le_antisymm
  · apply iSup_le
    intro x
    exact le_iSup (fun y : A => ENNReal.ofReal |f y|) ⟨φ x, x.property⟩
  · apply iSup_le
    intro y
    obtain ⟨x, hx⟩ := hφ y
    have hm : x ∈ φ ⁻¹' A := by simpa only [mem_preimage, hx] using y.property
    simpa only [Function.comp_apply, hx] using
      (le_iSup (fun x : φ ⁻¹' A => ENNReal.ofReal |(f ∘ φ) x|) ⟨x, hm⟩)

/-- The exact Hölder scaling of a similarity on an arbitrary
subset. This uses the shared least-constant seminorm, with no regularity
of the scalar function beyond its finite Hölder seminorm (BB p. 339). -/
theorem holderSemi_similarity_pullback (φ : X → Y) (hφ : Function.Surjective φ)
    {R : ℝ} (hR : 0 < R) (hd : ∀ x y, dist (φ x) (φ y) = R * dist x y)
    (δ : ℝ≥0) (A : Set Y) (f : Y → ℝ) (hf : H2.holderSemi δ A f < ⊤) :
    H2.holderSemi δ (φ ⁻¹' A) (f ∘ φ) =
      ENNReal.ofReal (R ^ (δ : ℝ)) * H2.holderSemi δ A f := by
  let r := R ^ (δ : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hR _
  have hu : H2.holderSemi δ (φ ⁻¹' A) (f ∘ φ) ≤
      ENNReal.ofReal (r * (H2.holderSemi δ A f).toReal) := by
    apply H2.holderSemi_le_of_bound (mul_nonneg hr.le ENNReal.toReal_nonneg)
    intro x hx y hy
    have hb := H2.sub_le_holderSemi hf hx hy
    rw [hd, Real.mul_rpow hR.le dist_nonneg] at hb
    simpa only [Function.comp_apply, mul_assoc, mul_left_comm] using hb
  have ht : H2.holderSemi δ (φ ⁻¹' A) (f ∘ φ) < ⊤ := hu.trans_lt ENNReal.ofReal_lt_top
  have hlu : (H2.holderSemi δ (φ ⁻¹' A) (f ∘ φ)).toReal ≤
      r * (H2.holderSemi δ A f).toReal := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hr.le ENNReal.toReal_nonneg)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  have hl : H2.holderSemi δ A f ≤
      ENNReal.ofReal ((H2.holderSemi δ (φ ⁻¹' A) (f ∘ φ)).toReal / r) := by
    apply H2.holderSemi_le_of_bound (div_nonneg ENNReal.toReal_nonneg hr.le)
    intro x hx y hy
    obtain ⟨a, ha⟩ := hφ x
    obtain ⟨b, hb⟩ := hφ y
    have hma : a ∈ φ ⁻¹' A := by simpa only [mem_preimage, ha] using hx
    have hmb : b ∈ φ ⁻¹' A := by simpa only [mem_preimage, hb] using hy
    have hbound := H2.sub_le_holderSemi ht hma hmb
    have he : dist x y ^ (δ : ℝ) = r * dist a b ^ (δ : ℝ) := by
      rw [← ha, ← hb, hd, Real.mul_rpow hR.le dist_nonneg]
    rw [he, ← mul_assoc, div_mul_cancel₀ _ hr.ne']
    simpa only [Function.comp_apply, ha, hb] using hbound
  have hll : (H2.holderSemi δ A f).toReal ≤
      (H2.holderSemi δ (φ ⁻¹' A) (f ∘ φ)).toReal / r := by
    simpa only [ENNReal.toReal_ofReal (div_nonneg ENNReal.toReal_nonneg hr.le)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
  have he := le_antisymm hlu ((le_div_iff₀ hr).mp hll |> fun h => by simpa only [mul_comm] using h)
  rw [← ENNReal.ofReal_toReal ht.ne, he, ENNReal.ofReal_mul hr.le,
    ENNReal.ofReal_toReal hf.ne]

end RothschildStein.H3

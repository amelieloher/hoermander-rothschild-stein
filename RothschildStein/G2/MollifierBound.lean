-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierPointwise
public import RothschildStein.G2.MollifierIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- A group mollifier preserves a global pointwise bound
(BB Prop 3.48 proof, p. 122). -/
theorem norm_groupRegularize_le (φ : GroupMollifier G ν) {f : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {ε : ℝ}
    (hε : 0 < ε) (x : Fin N → ℝ) : ‖groupRegularize G φ f ε x‖ ≤ C := by
  have hφ : Integrable φ := φ.smooth.continuous.integrable_of_hasCompactSupport φ.compact
  have hmeas : AEStronglyMeasurable (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
    (φ.smooth.continuous.mul (hf.comp ((continuous_mul G).comp
      (((continuous_inv G).comp (continuous_dilate G ε)).prodMk continuous_const)))).aestronglyMeasurable
  have hb (z : Fin N → ℝ) :
      ‖φ z * f (G.mul (G.inv (G.dilate ε z)) x)‖ ≤ φ z * C := by
    rw [norm_mul, Real.norm_of_nonneg (φ.nonneg z)]
    exact mul_le_mul_of_nonneg_left (hC _) (φ.nonneg z)
  have hi : Integrable (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
    Integrable.mono' (hφ.mul_const C) hmeas (Filter.Eventually.of_forall fun z =>
      hb z)
  rw [groupRegularize_eq_integral G φ f hε]
  calc
    _ ≤ ∫ z, ‖φ z * f (G.mul (G.inv (G.dilate ε z)) x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, φ z * C := integral_mono hi.norm (hφ.mul_const C) hb
    _ = C := by rw [integral_mul_const, φ.integral_eq_one, one_mul]

/-- The dilates of a compact set with parameters in [0,1]
form a compact set (BB p. 122; common support). -/
theorem isCompact_small_dilates {s : Set (Fin N → ℝ)} (hs : IsCompact s) :
    IsCompact ((fun p : ℝ × (Fin N → ℝ) => G.dilate p.1 p.2) '' (Icc 0 1 ×ˢ s)) := by
  apply (isCompact_Icc.prod hs).image
  apply continuous_pi
  intro j
  exact (continuous_fst.pow (G.weight j)).mul ((continuous_apply j).comp continuous_snd)

/-- All regularizations with 0 < ε ≤ 1 of a compactly supported
input have one common compact support (BB p. 122; common support). -/
theorem exists_common_compact_support_groupRegularize (φ : GroupMollifier G ν)
    {f : (Fin N → ℝ) → ℝ} (hf : HasCompactSupport f) :
    ∃ K : Set (Fin N → ℝ), IsCompact K ∧ tsupport f ⊆ K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → Function.support (groupRegularize G φ f ε) ⊆ K := by
  let A := (fun p : ℝ × (Fin N → ℝ) => G.dilate p.1 p.2) '' (Icc 0 1 ×ˢ tsupport φ)
  let K := (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul p.1 p.2) '' (A ×ˢ tsupport f) ∪ tsupport f
  refine ⟨K, ((isCompact_small_dilates G φ.compact.isCompact).prod hf.isCompact).image
    (continuous_mul G) |>.union hf.isCompact, subset_union_right, ?_⟩
  intro ε hε he x hx
  have hs := support_groupConvolution_subset G (groupMollifierScale G φ ε) f hx
  rcases hs with ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
  apply Or.inl
  refine ⟨(y, z), ⟨?_, subset_closure hz⟩, rfl⟩
  have hp : φ (G.dilate ε⁻¹ y) ≠ 0 := by
    intro h
    apply hy
    simp only [groupMollifierScale, h, MulZeroClass.mul_zero]
  refine ⟨(ε, G.dilate ε⁻¹ y), ⟨⟨hε.le, he⟩, subset_closure hp⟩, ?_⟩
  change G.dilate ε (G.dilate ε⁻¹ y) = y
  rw [dilate_dilate, mul_inv_cancel₀ hε.ne', dilate_one]

end RothschildStein.G2

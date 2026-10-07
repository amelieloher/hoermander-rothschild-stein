-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FieldHomogeneity
public import RothschildStein.G2.DilationMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Tangent homogeneity gives dilation covariance of a
field acting on a function differentiable only at the dilated point. -/
theorem fieldDerivative_comp_dilate_at
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k : ℝ}
    (hV : G2.IsHomogeneousField G V k) {f : (Fin N → ℝ) → ℝ}
    {t : ℝ} (ht : 0 < t) (x : Fin N → ℝ)
    (hf : DifferentiableAt ℝ f (G.dilate t x)) :
    fieldDerivative V (f ∘ G.dilate t) x = t ^ k * fieldDerivative V f (G.dilate t x) := by
  unfold fieldDerivative
  rw [fderiv_comp x hf (G2.hasFDerivAt_dilate G t x).differentiableAt,
    (G2.hasFDerivAt_dilate G t x).fderiv]
  change fderiv ℝ f (G.dilate t x) (G2.dilationDifferential G t (V x)) = _
  rw [G2.dilationDifferential_apply, hV t ht x, map_smul]
  rfl

/-- Differentiating a punctured C¹ homogeneous kernel
subtracts the field degree, without requiring a globally smooth extension. -/
theorem fieldDerivative_punctured_homogeneity
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k β : ℝ}
    (hV : G2.IsHomogeneousField G V k) {f : (Fin N → ℝ) → ℝ}
    (hc : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    {t : ℝ} (ht : 0 < t) {x : Fin N → ℝ} (hx : x ≠ 0) :
    fieldDerivative V f (G.dilate t x) = t ^ (β - k) * fieldDerivative V f x := by
  have hd : G.dilate t x ≠ 0 := by
    intro he
    exact hx ((G2.dilate_bijective G ht.ne').injective (he.trans (G2.dilate_zero G t).symm))
  have hf : DifferentiableAt ℝ f (G.dilate t x) :=
    (hc.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hd))).differentiableAt (by norm_num)
  have he : (f ∘ G.dilate t) =ᶠ[𝓝 x] fun y => t ^ β * f y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show x ∈ {(0 : Fin N → ℝ)}ᶜ by simpa using hx)] with y hy
    exact hhom t ht y (by simpa using hy)
  have hop := fieldDerivative_comp_dilate_at G hV ht x hf
  have hder : fderiv ℝ (f ∘ G.dilate t) x = fderiv ℝ (fun y => t ^ β * f y) x := he.fderiv_eq
  have hscale : fieldDerivative V (f ∘ G.dilate t) x = t ^ β * fieldDerivative V f x := by
    unfold fieldDerivative
    rw [hder]
    change fderiv ℝ ((t ^ β) • f) x (V x) = _
    rw [fderiv_const_smul_field]
    rfl
  rw [hscale] at hop
  apply mul_left_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht k))
  rw [← mul_assoc, ← Real.rpow_add ht]
  have hk : k + (β - k) = β := by ring
  rw [hk]
  exact hop.symm

end RothschildStein.H1

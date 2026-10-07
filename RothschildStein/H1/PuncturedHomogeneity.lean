-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousBounds
public import RothschildStein.H1.Standing
public import RothschildStein.G2.FieldHomogeneity
public import RothschildStein.S.Transposes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A homogeneous field lowers the degree of a punctured smooth
function by its own degree (BB Theorem 6.20(1), printed p. 270).
The local formulation applies to singular fundamental kernels. -/
theorem fieldDerivative_punctured_homogeneous
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {a b : ℝ}
    (hV : G2.IsHomogeneousField G V b)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ({(0 : Fin N → ℝ)}ᶜ))
    (hh : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x)
    {t : ℝ} (ht : 0 < t) {x : Fin N → ℝ} (hx : x ≠ 0) :
    fieldDerivative V f (G.dilate t x) = t ^ (a - b) * fieldDerivative V f x := by
  have htx : G.dilate t x ≠ 0 := by
    intro hz
    apply hx
    apply (G2.dilate_bijective G ht.ne').injective
    simpa only [G2.dilate_zero] using hz
  have hdf : DifferentiableAt ℝ f (G.dilate t x) :=
    (hf.contDiffAt (isOpen_compl_singleton.mem_nhds htx)).differentiableAt (by simp)
  have hdx : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  have he : (f ∘ G.dilate t) =ᶠ[𝓝 x] (fun y => t ^ a * f y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact hh t ht y hy
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x hdf (G2.hasFDerivAt_dilate G t x).differentiableAt,
    (G2.hasFDerivAt_dilate G t x).fderiv] at hd
  have hc : fderiv ℝ (fun y => t ^ a * f y) x = t ^ a • fderiv ℝ f x :=
    (hdx.hasFDerivAt.const_mul (t ^ a)).fderiv
  rw [hc] at hd
  have hv := congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (V x)) hd
  change fderiv ℝ f (G.dilate t x) (G2.dilationDifferential G t (V x)) = _ at hv
  rw [G2.dilationDifferential_apply, hV t ht x, map_smul] at hv
  change t ^ b * fieldDerivative V f (G.dilate t x) = t ^ a * fieldDerivative V f x at hv
  rw [Real.rpow_sub ht]
  have hn : t ^ b ≠ 0 := (Real.rpow_pos_of_pos ht b).ne'
  apply (mul_left_cancel₀ hn)
  rw [← mul_assoc]
  field_simp
  exact hv

end RothschildStein.H1

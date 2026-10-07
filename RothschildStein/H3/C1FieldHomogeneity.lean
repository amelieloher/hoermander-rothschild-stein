-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FieldHomogeneity
public import RothschildStein.G2.Algebra
public import RothschildStein.G2.DilationMeasure
public import RothschildStein.H3.SphereMaximum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A homogeneous field differentiates a punctured C¹
homogeneous function to the expected degree. Only one scalar derivative
is used, matching BB Proposition 6.25, pp. 272–273. -/
theorem fieldDerivative_homogeneous_C1 {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f {0}ᶜ) {a m : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : G2.IsHomogeneousField G V m)
    {t : ℝ} (ht : 0 < t) {x : Fin N → ℝ} (hx : x ≠ 0) :
    fieldDerivative V f (G.dilate t x) = t ^ (a - m) * fieldDerivative V f x := by
  have hdx : G.dilate t x ≠ 0 := by
    intro he
    apply hx
    apply (G2.dilate_bijective G ht.ne').injective
    simpa only [G2.dilate_zero] using he
  have hfx : DifferentiableAt ℝ f x :=
    ((hf.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by norm_num))
  have hfd : DifferentiableAt ℝ f (G.dilate t x) :=
    ((hf.contDiffAt (isOpen_compl_singleton.mem_nhds hdx)).differentiableAt (by norm_num))
  have he : (f ∘ G.dilate t) =ᶠ[𝓝 x] (fun z => t ^ a * f z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz
    exact hhom t ht z hz
  have hd₁ := hfd.hasFDerivAt.comp x (G2.hasFDerivAt_dilate G t x)
  have hd₂ := (hfx.hasFDerivAt.const_mul (t ^ a)).congr_of_eventuallyEq he
  have hb := congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (V x)) (hd₁.unique hd₂)
  change fderiv ℝ f (G.dilate t x) (G.dilate t (V x)) =
    t ^ a * fderiv ℝ f x (V x) at hb
  rw [hV t ht x, map_smul, smul_eq_mul] at hb
  unfold fieldDerivative
  calc
    _ = (t ^ a * fderiv ℝ f x (V x)) / t ^ m :=
      (eq_div_iff (Real.rpow_pos_of_pos ht m).ne').mpr (by simpa only [mul_comm] using hb)
    _ = _ := by rw [mul_div_right_comm, ← Real.rpow_sub ht]

/-- The directional derivative is continuous on the punctured
space with only C¹ regularity of the scalar kernel. -/
theorem fieldDerivative_continuousOn_C1 {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f {0}ᶜ) {V : (Fin N → ℝ) → (Fin N → ℝ)}
    (hV : ContinuousOn V {0}ᶜ) : ContinuousOn (fieldDerivative V f) {0}ᶜ :=
  (hf.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl).clm_apply hV

/-- The exact sphere maximum bounds a homogeneous directional
derivative everywhere off the identity, using only punctured C¹ data. -/
theorem fieldDerivative_sphere_power_bound_C1
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContDiffOn ℝ 1 f {0}ᶜ) {a m : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x)
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hVc : ContinuousOn V {0}ᶜ) (hV : G2.IsHomogeneousField G V m)
    (x : Fin N → ℝ) (hx : x ≠ 0) :
    |fieldDerivative V f x| ≤ kernelSphereBound ν (fieldDerivative V f) * ν x ^ (a - m) :=
  kernelSphereBound_homogeneous hν (fieldDerivative_continuousOn_C1 hf hVc)
    (fun _t ht _x hx => fieldDerivative_homogeneous_C1 G hf hhom V hV ht hx) x hx

end RothschildStein.H3

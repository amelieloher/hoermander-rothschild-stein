-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open SchwartzMap
namespace RothschildStein.Distribution
variable {N : ℕ}

/-- complexify any continuous real-linear
Schwartz functional by its real and imaginary test components. -/
def complexifySchwartzFunctional
    (L : SchwartzMap (Fin N → ℝ) ℝ →L[ℝ] ℂ) :
    TemperedDistribution (Fin N → ℝ) ℂ where
  toFun φ := L (SchwartzMap.postcompCLM Complex.reCLM φ) +
    Complex.I * L (SchwartzMap.postcompCLM Complex.imCLM φ)
  map_add' φ ψ := by
    simp only [map_add, mul_add]
    ring
  map_smul' c φ := by
    have hre : SchwartzMap.postcompCLM Complex.reCLM (c • φ) =
        c.re • SchwartzMap.postcompCLM Complex.reCLM φ -
          c.im • SchwartzMap.postcompCLM Complex.imCLM φ := by
      ext x
      simp only [SchwartzMap.postcompCLM_apply, smul_apply,
        sub_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul,
        Complex.mul_re]
    have him : SchwartzMap.postcompCLM Complex.imCLM (c • φ) =
        c.im • SchwartzMap.postcompCLM Complex.reCLM φ +
          c.re • SchwartzMap.postcompCLM Complex.imCLM φ := by
      ext x
      simp only [SchwartzMap.postcompCLM_apply, smul_apply,
        add_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul,
        Complex.mul_im]
      ring
    rw [hre, him]
    simp only [map_sub, map_add, map_smul, smul_eq_mul, RingHom.id_apply]
    simp only [Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring_nf
    simp only [Complex.I_sq]
    ring
  cont := by
    exact (L.continuous.comp (SchwartzMap.postcompCLM Complex.reCLM).continuous).add
      (continuous_const.mul (L.continuous.comp (SchwartzMap.postcompCLM Complex.imCLM).continuous))

end RothschildStein.Distribution

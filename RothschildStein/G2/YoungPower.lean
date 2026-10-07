-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.YoungHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The integrated finite-output Hölder bound. The three weights
are explicit so that endpoint zero weights require no limiting argument
(BB Prop 3.45, p. 119). -/
theorem lintegral_lgroupConvolution_rpow_le {f g : (Fin N → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {p q r a b c : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 1) (hp : p * (a + b) = 1) (hq : q * (a + c) = 1)
    (har : a * r = 1) :
    (∫⁻ x, lgroupConvolution G f g x ^ r) ≤
      ((∫⁻ y, f y ^ p) * (∫⁻ y, g y ^ q)) *
        (∫⁻ y, f y ^ p) ^ (b * r) * (∫⁻ y, g y ^ q) ^ (c * r) := by
  have hx (x : Fin N → ℝ) :=
    ENNReal.rpow_le_rpow (lgroupConvolution_three_holder G hf hg ha hb hc hs hp hq x) hr.le
  have hpow (x : Fin N → ℝ) :
      ((lgroupConvolution G (fun y => f y ^ p) (fun y => g y ^ q) x) ^ a *
        (∫⁻ y, f y ^ p) ^ b * (∫⁻ y, g y ^ q) ^ c) ^ r =
      lgroupConvolution G (fun y => f y ^ p) (fun y => g y ^ q) x *
        (∫⁻ y, f y ^ p) ^ (b * r) * (∫⁻ y, g y ^ q) ^ (c * r) := by
    simp only [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
      har, ENNReal.rpow_one]
  calc
    _ ≤ ∫⁻ x, ((lgroupConvolution G (fun y => f y ^ p) (fun y => g y ^ q) x) ^ a *
        (∫⁻ y, f y ^ p) ^ b * (∫⁻ y, g y ^ q) ^ c) ^ r := lintegral_mono hx
    _ = ∫⁻ x, lgroupConvolution G (fun y => f y ^ p) (fun y => g y ^ q) x *
        (∫⁻ y, f y ^ p) ^ (b * r) * (∫⁻ y, g y ^ q) ^ (c * r) := lintegral_congr hpow
    _ = _ := by
      rw [lintegral_mul_const _ ((measurable_lgroupConvolution G
        (hf.pow_const p) (hg.pow_const q)).mul_const _),
        lintegral_mul_const _ (measurable_lgroupConvolution G (hf.pow_const p) (hg.pow_const q)),
        lintegral_lgroupConvolution G (hf.pow_const p) (hg.pow_const q)]

end RothschildStein.G2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.NonnegativeConvolution
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The three-factor Hölder step in Young's inequality, allowing zero
weights and infinite integrals (BB Prop 3.45, p. 119). -/
theorem lgroupConvolution_three_holder {f g : (Fin N → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {p q a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1)
    (hp : p * (a + b) = 1) (hq : q * (a + c) = 1) (x : Fin N → ℝ) :
    lgroupConvolution G f g x ≤
      (lgroupConvolution G (fun y => f y ^ p) (fun y => g y ^ q) x) ^ a *
        (∫⁻ y, f y ^ p) ^ b * (∫⁻ y, g y ^ q) ^ c := by
  let F : Fin 3 → (Fin N → ℝ) → ℝ≥0∞ :=
    ![fun y => f y ^ p * g (G.mul (G.inv y) x) ^ q,
      fun y => f y ^ p, fun y => g (G.mul (G.inv y) x) ^ q]
  let w : Fin 3 → ℝ := ![a, b, c]
  have hgx : Measurable (fun y => g (G.mul (G.inv y) x)) :=
    hg.comp (measurePreserving_invRightAt G x).measurable
  have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (F i) volume := by
    intro i _
    fin_cases i
    · exact ((hf.pow_const p).mul (hgx.pow_const q)).aemeasurable
    · exact (hf.pow_const p).aemeasurable
    · exact (hgx.pow_const q).aemeasurable
  have hsum : ∑ i : Fin 3, w i = 1 := by simpa [w, Fin.sum_univ_succ, add_assoc] using hs
  have hpos : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have H := ENNReal.lintegral_prod_norm_pow_le Finset.univ hmeas hsum hpos
  have he (u v : ℝ≥0∞) : (u ^ p * v ^ q) ^ a * (u ^ p) ^ b * (v ^ q) ^ c = u * v := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha]
    calc
      (u ^ p) ^ a * (v ^ q) ^ a * (u ^ p) ^ b * (v ^ q) ^ c =
          ((u ^ p) ^ a * (u ^ p) ^ b) * ((v ^ q) ^ a * (v ^ q) ^ c) := by ac_rfl
      _ = u * v := by
        rw [← ENNReal.rpow_add_of_nonneg a b ha hb,
          ← ENNReal.rpow_add_of_nonneg a c ha hc,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hp, hq,
          ENNReal.rpow_one, ENNReal.rpow_one]
  have hi : (∫⁻ y, g (G.mul (G.inv y) x) ^ q) = ∫⁻ y, g y ^ q :=
    (measurePreserving_invRightAt G x).lintegral_comp ((hg.pow_const q))
  simpa only [F, w, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, ← _root_.mul_assoc, he, hi, lgroupConvolution_def] using H

end RothschildStein.G2

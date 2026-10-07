-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.DualMomentLimit
public import RothschildStein.H2.IntegralPairing

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Duality transfers the transpose's conjugate-exponent Lᵖ bound to the operator through the L² adjointness identity (BB p. 326). -/
theorem operator_lp_of_transpose_bound (μ : Measure X) [IsFiniteMeasure μ]
    (T Ts : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {p q C : ℝ}
    (hpq : p.HolderConjugate q) (hC : 0 ≤ C)
    (hadj : ∀ v w : Lp ℝ 2 μ, (∫ x, (T v) x * w x ∂μ) = ∫ x, v x * (Ts w) x ∂μ)
    (hTs : ∀ w : Lp ℝ 2 μ, MemLp w (ENNReal.ofReal q) μ →
      MemLp (fun x => (Ts w) x) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun x => (Ts w) x) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C * eLpNorm w (ENNReal.ofReal q) μ)
    (v : Lp ℝ 2 μ) (hvp : MemLp v (ENNReal.ofReal p) μ) :
    MemLp (fun x => (T v) x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => (T v) x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal p) μ := by
  have hb := lp_bound_of_l2_pairing (H := C * (eLpNorm v (ENNReal.ofReal p) μ).toReal) μ (T v) hpq.lt hpq.symm.pos
    (mul_nonneg hC ENNReal.toReal_nonneg) hpq.sub_one_mul_conj
    (by simpa only [one_div] using hpq.inv_add_inv_eq_one) ?_
  · refine ⟨hb.1, hb.2.trans_eq ?_⟩
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hvp.ne]
  · intro w hwq
    obtain ⟨hTsw, hn⟩ := hTs w hwq
    have ht : ENNReal.ofReal C * eLpNorm w (ENNReal.ofReal q) μ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwq.ne
    have hnreal : (eLpNorm (fun x => (Ts w) x) (ENNReal.ofReal q) μ).toReal ≤
        C * (eLpNorm w (ENNReal.ofReal q) μ).toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ht hn
    rw [hadj]
    calc
      _ ≤ (eLpNorm v (ENNReal.ofReal p) μ).toReal *
          (eLpNorm (fun x => (Ts w) x) (ENNReal.ofReal q) μ).toReal :=
        integral_pairing_le_eLpNorm μ hpq hvp hTsw
      _ ≤ (eLpNorm v (ENNReal.ofReal p) μ).toReal *
          (C * (eLpNorm w (ENNReal.ofReal q) μ).toReal) :=
        mul_le_mul_of_nonneg_left hnreal ENNReal.toReal_nonneg
      _ = _ := by ring

end RothschildStein.H2

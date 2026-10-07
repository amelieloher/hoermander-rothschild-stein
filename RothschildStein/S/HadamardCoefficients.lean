-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SmoothIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- The coefficient difference quotient appearing in the
Friedrichs transfer kernel (BB (2.8),(2.11), pp. 75–78). -/
def coefficientDifferenceQuotient (b : (Fin n → ℝ) → ℝ)
    (ε : ℝ) (x y : Fin n → ℝ) : ℝ := ε⁻¹ * (b (x+ε • y)-b x)

/-- Hadamard's integral gives the smooth extension of the
coefficient quotient across ε=0 (BB p. 76). -/
def hadamardCoefficient (b : (Fin n → ℝ) → ℝ)
    (p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ b (p.1.1+(t*p.2) • p.1.2) p.1.2

/-- Fundamental theorem of calculus along a coefficient segment
(BB p. 76; Hadamard). -/
theorem coefficient_segment_integral {b : (Fin n → ℝ) → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (x v : Fin n → ℝ) :
    (∫ t in (0 : ℝ)..1, fderiv ℝ b (x+t • v) v) = b (x+v)-b x := by
  have hd (t : ℝ) : HasDerivAt (fun t => b (x+t • v))
      (fderiv ℝ b (x+t • v) v) t := by
    have ht : HasDerivAt (fun t : ℝ => x+t • v) v t := by
      simpa only [id_eq,one_smul] using! ((hasDerivAt_id t).smul_const v).const_add x
    exact (hb.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t ht
  have hc : Continuous (fun t : ℝ => fderiv ℝ b (x+t • v) v) := by
    have hh : Continuous (fun t : ℝ => x+t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact ((hb.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)).continuous.comp hh).clm_apply
      continuous_const
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 1)
  simpa only [one_smul,zero_smul,add_zero] using H

/-- The actual quotient agrees with its Hadamard extension
at every nonzero parameter (BB p. 76). -/
theorem coefficientDifferenceQuotient_eq_hadamard {b : (Fin n → ℝ) → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) {ε : ℝ} (hε : ε ≠ 0) (x y : Fin n → ℝ) :
    coefficientDifferenceQuotient b ε x y = hadamardCoefficient b ((x,y),ε) := by
  have H := coefficient_segment_integral hb x (ε • y)
  have hf : (fun t : ℝ => fderiv ℝ b (x+t • (ε • y)) (ε • y)) =
      fun t => ε * fderiv ℝ b (x+(t*ε) • y) y := by
    funext t
    rw [smul_smul,ContinuousLinearMap.map_smul,smul_eq_mul]
  rw [hf,intervalIntegral.integral_const_mul] at H
  change ε⁻¹ * (b (x+ε • y)-b x) = _
  rw [← H]
  change ε⁻¹ * (ε * hadamardCoefficient b ((x,y),ε)) = _
  rw [← mul_assoc,inv_mul_cancel₀ hε,one_mul]

/-- The quotient extension depends jointly smoothly on x,y,ε
(BB p. 76; preferred joint-parameter encoding of the Hadamard). -/
theorem contDiff_hadamardCoefficient {b : (Fin n → ℝ) → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (hadamardCoefficient b) := by
  apply contDiff_unitIntervalIntegral
  let A := ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun p : A × ℝ => p.1.1.1) :=
    contDiff_fst.fst.fst
  have hy : ContDiff ℝ (⊤ : ℕ∞) (fun p : A × ℝ => p.1.1.2) :=
    contDiff_fst.fst.snd
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun p : A × ℝ => p.1.2) := contDiff_fst.snd
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun p : A × ℝ => p.2) := contDiff_snd
  have hp := hx.add ((ht.mul he).smul hy)
  exact ((hb.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)).comp hp).clm_apply hy

end RothschildStein.S

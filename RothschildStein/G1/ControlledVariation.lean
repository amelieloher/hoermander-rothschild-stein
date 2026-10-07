-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledDisplacement
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RothschildStein.G1

/-- Scalar variation along an actual controlled curve follows from
absolute continuity and coordinate FTC; measurable controls are never
sampled at a selected time (BB Thms 1.54/1.56, pp. 36–37). -/
theorem controlledCurve_variation_le {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    {δ C : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ∑ i, δ ^ (w i : ℕ) * |fderiv ℝ f (γ t) (X i (γ t))| ≤ C) :
    |f (γ 1) - f (γ 0)| ≤ C := by
  have hac := absolutelyContinuousOnInterval_comp_contDiffOn hΩ hf hγ.2.1
    (by simpa only [uIcc_of_le zero_le_one] using hγ.2.2.1)
  obtain ⟨a, _, ha⟩ := hγ.2.2.2
  have hae := (ae_restrict_iff' measurableSet_Icc).mp ha
  have hm : ‖∫ t in (0 : ℝ)..1, deriv (f ∘ γ) t‖ ≤ C * |1 - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [hae] with t ht htime
    have hI : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc htime
    have hd := ((hf.contDiffAt (hΩ.mem_nhds (hγ.2.2.1 hI))).differentiableAt
      one_ne_zero).hasFDerivAt.comp_hasDerivAt t (ht hI).2
    rw [hd.deriv, map_sum]
    calc
      ‖∑ i, fderiv ℝ f (γ t) (a i t • X i (γ t))‖ ≤
          ∑ i, ‖fderiv ℝ f (γ t) (a i t • X i (γ t))‖ := norm_sum_le _ _
      _ = ∑ i, |a i t| * |fderiv ℝ f (γ t) (X i (γ t))| := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, δ ^ (w i : ℕ) * |fderiv ℝ f (γ t) (X i (γ t))| :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right ((ht hI).1 i) (abs_nonneg _))
      _ ≤ C := hbound t hI
  simpa only [hac.integral_deriv_eq_sub, Function.comp_apply, sub_zero, abs_one,
    mul_one, Real.norm_eq_abs] using hm

/-- The exact horizontal coefficient constant is √q for the
separate component control bounds in the definition
(BB Thms 1.54/1.56, pp. 36–37). -/
theorem horizontal_abs_sum_le {q : ℕ} (v : Fin q → ℝ) :
    ∑ i, |v i| ≤ Real.sqrt q * Real.sqrt (∑ i, (v i) ^ 2) := by
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |v i|) (fun _ => (1 : ℝ))
      |>.trans_eq (mul_comm _ _)

end RothschildStein.G1

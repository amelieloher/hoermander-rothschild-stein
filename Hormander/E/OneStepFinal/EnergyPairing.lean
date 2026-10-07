-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.EnergyQ

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate ComplexInnerProductSpace

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

theorem hermitianPairing_eq_inner' (u v : TestFunction N) :
    hermitianPairing u v = inner ℂ (v.toLp 2) (u.toLp 2) := by
  rw [MeasureTheory.L2.inner_def]
  unfold hermitianPairing
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp v 2 volume, SchwartzMap.coeFn_toLp u 2 volume] with x hv hu
  rw [hv, hu]
  simp

theorem sobolevNorm_zero_sq' (u : TestFunction N) :
    sobolevNorm 0 u ^ 2 = Hormander.C.normSq u := by
  have h := Hormander.C.H_self u
  rw [hermitianPairing_eq_inner', inner_self_eq_norm_sq_to_K] at h
  rw [sobolevNorm_zero_order]
  apply Complex.ofReal_injective
  push_cast
  exact h

theorem sobolevNorm_zero_eq_sqrt (u : TestFunction N) :
    sobolevNorm 0 u = Real.sqrt (Hormander.C.normSq u) := by
  rw [← sobolevNorm_zero_sq', Real.sqrt_sq (sobolevNorm_nonneg _ _)]

/-- Pairing of `X g` with a test function, for `g ∈ L²`. -/
theorem exists_pair_vf_bound (V : RealSchwartzVectorField N) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (g : Tempered N) (B : ℝ) (φ : TestFunction N), Bdd 0 g B →
      ‖Eop (vectorFieldOperator V) g φ‖ ≤
        B * (sobolevNorm 0 (vectorFieldOperator V φ) + D * sobolevNorm 0 φ) := by
  have hM : HasOrder 0 (realMultiplierOperator (vectorFieldDivergence V)) :=
    hasOrder_multiplierOperator_zero (complexifyRealSchwartz _)
  obtain ⟨D, hD⟩ := hM 0
  refine ⟨D, D.2, fun g B φ hg => ?_⟩
  rw [Eop_apply (hct_vf V) (vectorFieldOperator_transpose V)]
  refine (hg.pairing _).trans ?_
  apply mul_le_mul_of_nonneg_left _ hg.nonneg
  have h1 : sobolevNorm 0 (-(vectorFieldOperator V) φ - realMultiplierOperator (vectorFieldDivergence V) φ) ≤
      sobolevNorm 0 (vectorFieldOperator V φ) +
        sobolevNorm 0 (realMultiplierOperator (vectorFieldDivergence V) φ) := by
    have e : -(vectorFieldOperator V) φ - realMultiplierOperator (vectorFieldDivergence V) φ =
        (-1 : ℂ) • vectorFieldOperator V φ + (-1 : ℂ) • realMultiplierOperator (vectorFieldDivergence V) φ := by
      simp [sub_eq_add_neg]
    rw [e]
    refine (sobolevNorm_add_le _ _ _).trans ?_
    rw [sobolevNorm_smul, sobolevNorm_smul]
    simp
  refine h1.trans (add_le_add le_rfl ?_)
  simpa using hD φ

end Hormander.E

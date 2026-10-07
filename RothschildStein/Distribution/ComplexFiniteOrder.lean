-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.TestOperators
public import Mathlib.Analysis.Distribution.Distribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology Distributions
namespace RothschildStein.Distribution
variable {n : ℕ}

/-- a complex-valued distribution on real tests
has finite order on each compact support. -/
theorem distribution_finite_order_complex (Ω : Opens (Fin n → ℝ))
    (T : Distribution Ω ℂ (⊤ : ℕ∞)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω) :
    ∃ (r : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : ContDiffMapSupportedIn (Fin n → ℝ) ℝ (⊤ : ℕ∞) K,
      ‖T (TestFunction.ofSupportedIn hK φ)‖ ≤
        C * ContDiffMapSupportedIn.supSeminorm ℝ (Fin n → ℝ) ℝ (⊤ : ℕ∞) K r φ := by
  let L := T.comp (TestFunction.ofSupportedInCLM ℝ hK)
  let q := (normSeminorm ℝ ℂ).comp L.toLinearMap
  have hq : Continuous q := continuous_norm.comp L.continuous
  obtain ⟨s, C, _, hb⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ (Fin n → ℝ) ℝ (⊤ : ℕ∞) K) q hq
  have hs : s ⊆ Finset.Iic (s.sup id) := by
    intro j hj
    exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) hj)
  refine ⟨s.sup id, C, C.coe_nonneg, fun φ => ?_⟩
  have hp := (Finset.sup_mono hs : s.sup
    (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ (⊤ : ℕ∞) K) ≤
    (Finset.Iic (s.sup id)).sup
      (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ (⊤ : ℕ∞) K)) φ
  have hh := hb φ
  change ‖T (TestFunction.ofSupportedIn hK φ)‖ ≤
    (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ (⊤ : ℕ∞) K)) φ at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hp C.coe_nonneg)

end RothschildStein.Distribution

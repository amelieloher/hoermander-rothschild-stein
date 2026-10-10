-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionScaling
public import HeatKernel.Moser.SmoothLocalEnergy
public import HeatKernel.Moser.StationaryTests

/-! # Affine changes of local weak solutions

Constant functions solve every homogeneous divergence equation considered here.
Adding a constant to a scalar multiple therefore preserves the literal local weak class.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace RothschildStein
open scoped BigOperators

namespace HeatKernel

variable {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}

/-- A constant function is a local weak solution for arbitrary coefficients. -/
theorem isLocalWeakSolution_const (c : ℝ) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U (fun _ _ => c) := by
  apply isLocalWeakSolution_of_contDiff_of_testIdentity G hq hqpos hw hspan a I U
    (u := fun _ => c) contDiff_const
  intro φ hφ hc _
  simp only [fderiv_const_apply, zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  have hi : Integrable (fun z : ℝ × (Fin N → ℝ) => c * fderiv ℝ φ z (1, 0)) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (1, 0))).const_mul c
  refine ⟨hi.neg, ?_⟩
  rw [integral_neg]
  apply neg_eq_zero.mpr
  have hz := integral_stationary_mul_fderiv_time_eq_zero_of_integrable
    (μ := (volume : Measure (Fin N → ℝ))) (u := fun _ => c) hφ hc
    (by rw [← Measure.volume_eq_prod]; exact hi)
  rw [← Measure.volume_eq_prod] at hz
  exact hz

/-- Affine changes preserve the local weak solution class. -/
theorem IsLocalWeakSolution.affine {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) (c d : ℝ) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => c * u t x + d) := by
  exact IsLocalWeakSolution.add G hq hqpos hw hspan
    (IsLocalWeakSolution.const_mul G hq hqpos hw hspan hu c)
    (isLocalWeakSolution_const G hq hqpos hw hspan d)

/-- Subtracting a constant preserves the local weak solution class. -/
theorem IsLocalWeakSolution.sub_const {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) (m : ℝ) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => u t x - m) := by
  simpa only [one_mul, sub_eq_add_neg] using
    IsLocalWeakSolution.affine G hq hqpos hw hspan hu 1 (-m)

/-- Subtracting a local weak solution from a constant preserves the same class. -/
theorem IsLocalWeakSolution.const_sub {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) (M : ℝ) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => M - u t x) := by
  simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using
    IsLocalWeakSolution.affine G hq hqpos hw hspan hu (-1) M

end HeatKernel

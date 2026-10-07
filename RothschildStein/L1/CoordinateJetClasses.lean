-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetDerivatives
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Ordered partials of a constant are either that constant or zero. -/
theorem rsPartial_const {N : ℕ} (J : List (Fin N)) (c : ℝ) :
    rsPartial J (fun _ : Fin N → ℝ => c) = if J = [] then (fun _ => c) else (fun _ => 0) := by
  induction J with
  | nil => simp only [rsPartial, ite_true]
  | cons j J ih =>
    simp only [rsPartial, ih, List.cons_ne_nil, ite_false]
    split_ifs <;> simp only [fderiv_const_apply, zero_apply]

/-- Actual coordinate functions have the expected constant first partial. -/
theorem rsPartial_coordinate_single {N : ℕ} (i j : Fin N) :
    rsPartial [j] (fun u : Fin N → ℝ => u i) = fun _ => (Pi.single j (1 : ℝ) : Fin N → ℝ) i := by
  funext u
  change fderiv ℝ ((ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ) : (Fin N → ℝ) → ℝ) u (Pi.single j 1) = _
  rw [ContinuousLinearMap.fderiv]
  rfl

/-- Every higher ordinary partial of a coordinate function is zero. -/
theorem rsPartial_coordinate_of_two_le {N : ℕ} (i : Fin N) (J : List (Fin N))
    (hJ : 2 ≤ J.length) : rsPartial J (fun u : Fin N → ℝ => u i) = fun _ => 0 := by
  revert hJ
  induction J using List.reverseRecOn with
  | nil => intro hJ; simp only [List.length_nil] at hJ; omega
  | append_singleton K j ih =>
    intro hJ
    rw [rsPartial_append_lists, rsPartial_coordinate_single, rsPartial_const]
    have hne : K ≠ [] := by intro h; subst K; simp only [List.nil_append, List.length_singleton] at hJ; omega
    simp only [hne, ite_false]

/-- Coordinates have their assigned scalar weight and zero value at the origin. -/
theorem circleScalarJetClass_coordinate {N p : ℕ} (Ω : Set (Fin N → ℝ))
    (ω : Fin N → ℕ) (i : Fin N) :
    circleScalarJetClass Ω ω (ω i : ℝ) p (fun u => u i) := by
  refine ⟨⟨contDiffOn_apply ℝ ℝ i Ω, ?_⟩, rfl⟩
  intro J hJ hw
  cases J with
  | nil => rfl
  | cons j J =>
    cases J with
    | nil =>
      rw [rsPartial_coordinate_single]
      have hji : j ≠ i := by
        intro h
        subst j
        have hh : (ω i : ℝ) < (ω i : ℝ) := by
          simpa only [List.map_singleton, List.sum_singleton] using hw
        exact (lt_irrefl (ω i : ℝ)) hh
      simp only [Pi.single_apply, Ne.symm hji, ite_false]
    | cons k J =>
      rw [rsPartial_coordinate_of_two_le i (j :: k :: J) (by simp)]
end RothschildStein.L1

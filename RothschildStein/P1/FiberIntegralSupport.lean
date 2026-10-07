-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- Each fiber section of a compactly supported function has
compact support, including when either coordinate block is empty. -/
theorem hasCompactSupport_fiberSection {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : HasCompactSupport F) (x : Fin n → ℝ) :
    HasCompactSupport (fun z => F (x, z)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hF.isCompact.image continuous_snd)
  intro z hz
  exact ⟨(x, z), subset_tsupport F hz, rfl⟩

/-- A continuous compactly supported test has an absolutely
integrable section on every fiber. -/
theorem integrable_fiberSection {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : Continuous F) (hFc : HasCompactSupport F) (x : Fin n → ℝ) :
    Integrable (fun z => F (x, z)) := by
  exact (hF.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (hasCompactSupport_fiberSection hFc x)

/-- Fiber integration has support in the base projection of
 the input support; this uses no totalized-integral regularity premise. -/
theorem support_fiberIntegral_subset {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (F : ((Fin n → ℝ) × (Fin d → ℝ)) → B) :
    Function.support (fun x => ∫ z, F (x, z)) ⊆ Prod.fst '' tsupport F := by
  classical
  intro x hx
  by_contra h
  apply hx
  have hz : ∀ z, F (x, z) = 0 := by
    intro z
    by_contra hf
    exact h ⟨(x, z), subset_tsupport F hf, rfl⟩
  simp only [hz, integral_zero]

/-- The topological support of the fiber integral is contained
in the compact base projection of the input topological support. -/
theorem tsupport_fiberIntegral_subset {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : HasCompactSupport F) :
    tsupport (fun x => ∫ z, F (x, z)) ⊆ Prod.fst '' tsupport F :=
  closure_minimal (support_fiberIntegral_subset F)
    (hF.isCompact.image continuous_fst).isClosed

/-- Fiber integration preserves compact support on the base. -/
theorem hasCompactSupport_fiberIntegral {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : HasCompactSupport F) :
    HasCompactSupport (fun x => ∫ z, F (x, z)) :=
  HasCompactSupport.of_support_subset_isCompact
    (hF.isCompact.image continuous_fst) (support_fiberIntegral_subset F)

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv
public import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}

/-- Field transposes preserve equality of germs (BB p. 68). -/
theorem fieldTranspose_eventuallyEq
    (V : (Fin n → ℝ) → (Fin n → ℝ)) {f g : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} (h : f =ᶠ[𝓝 x] g) : fieldTranspose V f =ᶠ[𝓝 x] fieldTranspose V g := by
  have hp : (fun y => f y • V y) =ᶠ[𝓝 x] fun y => g y • V y := h.smul .rfl
  filter_upwards [hp.fderiv (𝕜 := ℝ)] with y hy
  simp only [fieldTranspose, Hormander.Interface.euclideanDivergence, hy]

/-- Word transposes depend only on the germ of their input
(BB p. 68). -/
theorem wordTranspose_eventuallyEq
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : f =ᶠ[𝓝 x] g) :
    wordTranspose X I f =ᶠ[𝓝 x] wordTranspose X I g := by
  induction I generalizing f g with
  | nil => exact h
  | cons i I ih => exact ih (fieldTranspose_eventuallyEq (X i) h)

/-- A compact subset of an open set has a test cutoff equal to one on
an open neighbourhood (BB p. 73; zero-extension). -/
theorem exists_test_plateau (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω) :
    ∃ (χ : TestFunction Ω ℝ (⊤ : ℕ∞)) (U : Set (Fin n → ℝ)),
      IsOpen U ∧ (K : Set (Fin n → ℝ)) ⊆ U ∧ U ⊆ Ω ∧ EqOn χ 1 U := by
  obtain ⟨W, hW, hKW, hclW, hcW⟩ :=
    exists_open_between_and_isCompact_closure K.isCompact Ω.isOpen hK
  obtain ⟨U, hU, hKU, hclU, _⟩ :=
    exists_open_between_and_isCompact_closure K.isCompact hW hKW
  obtain ⟨χ, hχ, _, hs, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hclU
  have ht : tsupport χ ⊆ Ω := by rw [tsupport, hs]; exact hclW
  let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    ⟨χ, hχ, by simpa [HasCompactSupport, tsupport, hs] using hcW, ht⟩
  refine ⟨ψ, U, hU, hKU, subset_closure.trans (hclU.trans (subset_closure.trans hclW)), ?_⟩
  intro x hx
  exact (hone x).mp (subset_closure hx)

/-- A locally integrable function supported almost everywhere in an interior compact set has an integrable zero extension (BB pp. 67–69). -/
theorem integrable_zeroExtension_of_compact_support (Ω : Opens (Fin n → ℝ))
    (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ Ω)
    (f : (Fin n → ℝ) → ℝ) (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume)
    (hs : ∀ᵐ x ∂volume, x ∈ (Ω : Set (Fin n → ℝ)) → x ∉ K → f x = 0) :
    Integrable ((Ω : Set (Fin n → ℝ)).indicator f) volume := by
  have hi : Integrable ((K : Set (Fin n → ℝ)).indicator f) volume :=
    (integrable_indicator_iff K.isCompact.measurableSet).mpr
      (hf.integrableOn_compact_subset hK K.isCompact)
  apply hi.congr
  filter_upwards [hs] with x hx
  by_cases hmem : x ∈ (K : Set (Fin n → ℝ))
  · simp [Set.indicator_of_mem hmem, Set.indicator_of_mem (hK hmem)]
  · by_cases hΩ : x ∈ (Ω : Set (Fin n → ℝ))
    · simp [hmem, hΩ, hx hΩ hmem]
    · simp [hmem, hΩ]

end RothschildStein.S

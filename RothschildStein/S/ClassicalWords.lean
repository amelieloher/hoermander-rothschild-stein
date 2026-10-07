-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntegrationByParts
public import RothschildStein.Definitions.wordDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ContDiff
namespace RothschildStein.S
variable {n m : ℕ}

/-- Classical words of smooth fields preserve local smoothness (BB p. 68). -/
theorem contDiffOn_wordDerivative (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wordDerivative X I f) (Ω : Set (Fin n → ℝ)) := by
  induction I with
  | nil => exact hf
  | cons i I ih => exact contDiffOn_fieldDerivative Ω (X i) _ (hX i) ih

/-- For smooth functions, every classical word derivative is its weak
word derivative (BB Def. 2.1, p. 68). -/
theorem hasWeakWordDeriv_classical (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ))) :
    hasWeakWordDeriv X Ω I f (wordDerivative X I f) := by
  induction I with
  | nil =>
    exact hasWeakWordDeriv_nil X Ω
      (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
  | cons i I ih =>
    apply (hasWeakWordDeriv_cons_iff X Ω hX ih i).mpr
    have hs := contDiffOn_wordDerivative Ω X hX I f hf
    refine ⟨ih.2.1,
      (contDiffOn_fieldDerivative Ω (X i) _ (hX i) hs).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet, fun φ => ?_⟩
    exact integral_fieldDerivative_mul_test Ω (X i) (hX i) _ (hs.of_le (by simp)) φ

/-- A classical field derivative does not enlarge support (BB p. 68). -/
theorem tsupport_fieldDerivative_subset
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    tsupport (fieldDerivative V f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  exact hx (by simp [fieldDerivative, fderiv_of_notMem_tsupport ℝ h])

/-- Classical word derivatives do not enlarge support (BB p. 68). -/
theorem tsupport_wordDerivative_subset
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    (f : (Fin n → ℝ) → ℝ) : tsupport (wordDerivative X I f) ⊆ tsupport f := by
  induction I with
  | nil => exact Subset.rfl
  | cons i I ih => exact (tsupport_fieldDerivative_subset (X i) _).trans ih

/-- A smooth local word applied to a test is again a test (BB p. 68). -/
def wordDerivativeTest (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    TestFunction Ω ℝ (⊤ : ℕ∞) := by
  have hs := tsupport_wordDerivative_subset X I φ
  refine ⟨wordDerivative X I φ, ?_, φ.hasCompactSupport.of_isClosed_subset isClosed_closure hs,
    hs.trans φ.tsupport_subset⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
  · exact (contDiffOn_wordDerivative Ω X hX I φ φ.contDiff.contDiffOn).contDiffAt (Ω.isOpen.mem_nhds hx)
  · have hxs : x ∉ tsupport (wordDerivative X I φ) :=
      fun ht => hx (φ.tsupport_subset (hs ht))
    have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport (wordDerivative X I φ) :=
      isClosed_closure.isOpen_compl.mem_nhds hxs
    exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : Fin n → ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
        (he.mono fun y hy => image_eq_zero_of_notMem_tsupport hy)

/-- A classical word of length l loses exactly l orders of finite
local differentiability (BB p. 68). -/
theorem contDiffOn_wordDerivative_finite (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (k : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiffOn ℝ ((k + I.length : ℕ) : ℕ∞ω) f (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ k (wordDerivative X I f) (Ω : Set (Fin n → ℝ)) := by
  induction I generalizing k with
  | nil => simpa [wordDerivative] using hf
  | cons i I ih =>
    have he : k + (i :: I).length = (k + 1) + I.length := by simp; omega
    rw [he] at hf
    have hs := ih (k + 1) hf
    exact (hs.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply ((hX i).of_le (by simp))

/-- Classical and weak derivatives agree at exactly the finite
regularity required by the word length (BB p. 68). -/
theorem hasWeakWordDeriv_classical_finite (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiffOn ℝ I.length f (Ω : Set (Fin n → ℝ))) :
    hasWeakWordDeriv X Ω I f (wordDerivative X I f) := by
  induction I with
  | nil =>
    exact hasWeakWordDeriv_nil X Ω
      (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
  | cons i I ih =>
    have hle : (I.length : ℕ∞ω) ≤ ((i :: I).length : ℕ∞ω) := by simp
    have htail := ih (hf.of_le hle)
    apply (hasWeakWordDeriv_cons_iff X Ω hX htail i).mpr
    have hs : ContDiffOn ℝ 1 (wordDerivative X I f) (Ω : Set (Fin n → ℝ)) :=
      contDiffOn_wordDerivative_finite Ω X hX I 1 f (by simpa [Nat.add_comm] using hf)
    have hs0 := contDiffOn_wordDerivative_finite Ω X hX (i :: I) 0 f (by simpa using hf)
    exact ⟨htail.2.1, hs0.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet,
      fun φ => integral_fieldDerivative_mul_test Ω (X i) (hX i) _ hs φ⟩

end RothschildStein.S

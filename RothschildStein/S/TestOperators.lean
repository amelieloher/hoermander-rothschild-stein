-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Transposes
public import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}

/-- Smooth coefficients on an open set have a smooth extension agreeing
on any fixed compact subset (BB pp. 67–69). -/
theorem smooth_extension_on_compact (Ω : Opens (Fin n → ℝ))
    (a : (Fin n → ℝ) → ℝ) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ Ω) :
    ∃ b : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ EqOn b a K := by
  obtain ⟨W, hW, hKW, hclW, hcW⟩ :=
    exists_open_between_and_isCompact_closure K.isCompact Ω.isOpen hK
  obtain ⟨χ, hχ, _, hs, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW K.isCompact.isClosed hKW
  have ht : tsupport χ ⊆ Ω := by
    rw [tsupport, hs]
    exact hclW
  let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) := ⟨χ, hχ, by simpa [HasCompactSupport, tsupport, hs] using hcW, ht⟩
  refine ⟨testMultiplierOn Ω a ha ψ, (testMultiplierOn Ω a ha ψ).contDiff, ?_⟩
  intro x hx
  change χ x * a x = a x
  rw [(hχone x).mp hx, one_mul]

/-- A local smooth multiplier is continuous on test functions with fixed support (BB pp. 67–69). -/
theorem continuous_testMultiplierOn (Ω : Opens (Fin n → ℝ))
    (a : (Fin n → ℝ) → ℝ) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ))) :
    Continuous (testMultiplierOn Ω a ha) := by
  let T : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] TestFunction Ω ℝ (⊤ : ℕ∞) :=
    { toFun := testMultiplierOn Ω a ha
      map_add' := by intro f g; ext x; change (f x + g x) * a x = f x * a x + g x * a x; ring
      map_smul' := by intro c f; ext x; change (c * f x) * a x = c * (f x * a x); ring }
  change Continuous T
  apply (TestFunction.continuous_iff_continuous_comp T).mpr
  intro K hK
  obtain ⟨b, hb, he⟩ := smooth_extension_on_compact Ω a ha K hK
  have ht : T ∘ TestFunction.ofSupportedIn hK =
      (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hb) ∘
        TestFunction.ofSupportedIn hK := by
    funext φ
    ext x
    change φ x * a x = φ x * b x
    by_cases hx : x ∈ (K : Set (Fin n → ℝ))
    · rw [he hx]
    · rw [φ.zero_on_compl hx]
      simp
  rw [ht]
  exact (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hb).continuous.comp
    (TestFunction.continuous_ofSupportedIn hK)

/-- A local smooth multiplier defines a continuous linear map on test functions with fixed support (BB pp. 67–69). -/
def testMultiplierCLM (Ω : Opens (Fin n → ℝ))
    (a : (Fin n → ℝ) → ℝ) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ))) :
    TestFunction Ω ℝ (⊤ : ℕ∞) →L[ℝ] TestFunction Ω ℝ (⊤ : ℕ∞) where
  toFun := testMultiplierOn Ω a ha
  map_add' := by intro f g; ext x; change (f x + g x) * a x = f x * a x + g x * a x; ring
  map_smul' := by intro c f; ext x; change (c * f x) * a x = c * (f x * a x); ring
  cont := continuous_testMultiplierOn Ω a ha

/-- Field transposition is a continuous linear map on tests
(BB (2.2), p. 68; topology). -/
def fieldTransposeCLM (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ))) :
    TestFunction Ω ℝ (⊤ : ℕ∞) →L[ℝ] TestFunction Ω ℝ (⊤ : ℕ∞) :=
  -∑ j : Fin n, (TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec j)).comp
    (testMultiplierCLM Ω (fun x => V x j) ((contDiff_apply ℝ ℝ j).comp_contDiffOn hV))

/-- The continuous linear field transpose is the test transpose
(BB (2.2), p. 68). -/
theorem fieldTransposeCLM_apply (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    fieldTransposeCLM Ω V hV φ = fieldTransposeTest Ω V hV φ := by
  simp [fieldTransposeCLM, fieldTransposeTest, testMultiplierCLM]

/-- Composition gives a continuous linear word transpose
(BB p. 68; topology). -/
def wordTransposeCLM (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) :
    List (Fin m) → TestFunction Ω ℝ (⊤ : ℕ∞) →L[ℝ] TestFunction Ω ℝ (⊤ : ℕ∞)
  | [] => ContinuousLinearMap.id ℝ _
  | i :: I => (wordTransposeCLM Ω X hX I).comp (fieldTransposeCLM Ω (X i) (hX i))

/-- Continuous word transpose agrees with the operator (BB p. 68). -/
theorem wordTransposeCLM_apply (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    wordTransposeCLM Ω X hX I φ = wordTransposeTest Ω X hX I φ := by
  induction I generalizing φ with
  | nil => rfl
  | cons i I ih =>
    simp only [wordTransposeCLM, ContinuousLinearMap.comp_apply, wordTransposeTest,
      fieldTransposeCLM_apply, ih]

end RothschildStein.S

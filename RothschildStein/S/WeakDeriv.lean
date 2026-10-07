-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Transposes
public import RothschildStein.Definitions.hasWeakWordDeriv
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}
variable (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
variable (Ω : Opens (Fin n → ℝ))

/-- A locally integrable function times a test is integrable
(BB Def. 2.1, pp. 67–68). -/
theorem integrable_mul_test {f : (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Integrable (fun x => f x * φ x) volume := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f (φ : (Fin n → ℝ) → ℝ)).trans (subset_tsupport φ))).mp
  exact (hf.integrableOn_compact_subset φ.tsupport_subset φ.hasCompactSupport).mul_continuousOn φ.continuous.continuousOn φ.hasCompactSupport

/-- The empty weak word is the original locally integrable function
(BB Def. 2.1, pp. 67–68). -/
theorem hasWeakWordDeriv_nil {f : (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume) :
    hasWeakWordDeriv X Ω [] f f := by
  exact ⟨hf, hf, fun _ => rfl⟩

/-- Uniqueness of a weak word derivative up to null sets
(BB Def. 2.1, pp. 67–68; fundamental lemma). -/
theorem hasWeakWordDeriv_unique {I : List (Fin m)} {f g h : (Fin n → ℝ) → ℝ}
    (hg : hasWeakWordDeriv X Ω I f g) (hh : hasWeakWordDeriv X Ω I f h) :
    g =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] h := by
  have hz := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hg.2.1.sub hh.2.1) (fun φ hφ hc hs => ?_)
  · rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
    filter_upwards [hz] with x hx
    intro hmem
    exact sub_eq_zero.mp (hx hmem)
  · let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hc, hs⟩
    have hi := (hg.2.2 ψ).trans (hh.2.2 ψ).symm
    have hig := (integrable_mul_test Ω hg.2.1 ψ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
    have hih := (integrable_mul_test Ω hh.2.1 ψ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
    change (∫ x in (Ω : Set (Fin n → ℝ)), g x * φ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), h x * φ x at hi
    change IntegrableOn (fun x => g x * φ x) (Ω : Set (Fin n → ℝ)) volume at hig
    change IntegrableOn (fun x => h x * φ x) (Ω : Set (Fin n → ℝ)) volume at hih
    have he : (∫ x in (Ω : Set (Fin n → ℝ)), (g x - h x) * φ x) = 0 := by
      simp_rw [sub_mul]
      rw [integral_sub hig hih, hi, sub_self]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := (Ω : Set (Fin n → ℝ))) (fun x hx => by
        have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
        simp [hzero])]
    simpa only [smul_eq_mul, Pi.sub_apply, mul_comm] using he

/-- The one-shot cons word is precisely the derivative of its suffix
(BB p. 77; suffix). -/
theorem hasWeakWordDeriv_cons_iff
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {I : List (Fin m)} {f g h : (Fin n → ℝ) → ℝ}
    (hh : hasWeakWordDeriv X Ω I f h) (i : Fin m) :
    hasWeakWordDeriv X Ω (i :: I) f g ↔ hasWeakWordDeriv X Ω [i] h g := by
  constructor
  · intro hg
    refine ⟨hh.2.1, hg.2.1, fun φ => ?_⟩
    rw [hg.2.2 φ, wordTranspose, wordTranspose, wordTranspose]
    have hi := hh.2.2 (fieldTransposeTest Ω (X i) (hX i) φ)
    simpa only [fieldTransposeTest_coe] using hi.symm
  · intro hg
    refine ⟨hh.1, hg.2.1, fun φ => ?_⟩
    rw [hg.2.2 φ, wordTranspose, wordTranspose, wordTranspose]
    have hi := hh.2.2 (fieldTransposeTest Ω (X i) (hX i) φ)
    simpa only [fieldTransposeTest_coe] using hi

/-- Weak derivatives are additive (BB Def. 2.1, pp. 67–68). -/
theorem hasWeakWordDeriv_add
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {I : List (Fin m)} {f₁ f₂ g₁ g₂ : (Fin n → ℝ) → ℝ}
    (h₁ : hasWeakWordDeriv X Ω I f₁ g₁) (h₂ : hasWeakWordDeriv X Ω I f₂ g₂) :
    hasWeakWordDeriv X Ω I (fun x => f₁ x + f₂ x) (fun x => g₁ x + g₂ x) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun φ => ?_⟩
  have hleft₁ := (integrable_mul_test Ω h₁.2.1 φ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  have hleft₂ := (integrable_mul_test Ω h₂.2.1 φ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  have hright₁ := (integrable_mul_test Ω h₁.1 (wordTransposeTest Ω X hX I φ)).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  have hright₂ := (integrable_mul_test Ω h₂.1 (wordTransposeTest Ω X hX I φ)).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  rw [wordTransposeTest_apply] at hright₁ hright₂
  simp_rw [add_mul]
  rw [integral_add hleft₁ hleft₂, integral_add hright₁ hright₂, h₁.2.2 φ, h₂.2.2 φ]

/-- Weak derivatives commute with scalar multiplication (BB Def. 2.1, p. 68). -/
theorem hasWeakWordDeriv_smul {I : List (Fin m)} {f g : (Fin n → ℝ) → ℝ}
    (h : hasWeakWordDeriv X Ω I f g) (c : ℝ) :
    hasWeakWordDeriv X Ω I (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨h.1.smul c, h.2.1.smul c, fun φ => ?_⟩
  simp_rw [mul_assoc, integral_const_mul]
  rw [h.2.2 φ]

/-- Weak words restrict to any smaller open set (BB Def. 2.1, p. 68). -/
theorem hasWeakWordDeriv_restrict (U : Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    {I : List (Fin m)} {f g : (Fin n → ℝ) → ℝ}
    (h : hasWeakWordDeriv X Ω I f g) : hasWeakWordDeriv X U I f g := by
  refine ⟨h.1.mono_set hU, h.2.1.mono_set hU, fun φ => ?_⟩
  let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hU⟩
  have he := h.2.2 ψ
  have hg₁ : ∀ x, x ∉ (U : Set (Fin n → ℝ)) → g x * φ x = 0 :=
    fun x hx => by simp [φ.zero_on_compl hx]
  have hf₁ : ∀ x, x ∉ (U : Set (Fin n → ℝ)) → f x * wordTranspose X I φ x = 0 := by
    intro x hx
    have hz : wordTranspose X I φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (φ.tsupport_subset (tsupport_wordTranspose_subset X I φ ht)))
    simp [hz]
  have hg₂ : ∀ x, x ∉ (Ω : Set (Fin n → ℝ)) → g x * φ x = 0 :=
    fun x hx => hg₁ x (fun hu => hx (hU hu))
  have hf₂ : ∀ x, x ∉ (Ω : Set (Fin n → ℝ)) → f x * wordTranspose X I φ x = 0 :=
    fun x hx => hf₁ x (fun hu => hx (hU hu))
  change (∫ x in (U : Set (Fin n → ℝ)), g x * φ x) =
    ∫ x in (U : Set (Fin n → ℝ)), f x * wordTranspose X I φ x
  change (∫ x in (Ω : Set (Fin n → ℝ)), g x * φ x) =
    ∫ x in (Ω : Set (Fin n → ℝ)), f x * wordTranspose X I φ x at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hg₂,
    setIntegral_eq_integral_of_forall_compl_eq_zero hf₂] at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hg₁,
    setIntegral_eq_integral_of_forall_compl_eq_zero hf₁]
  exact he

/-- Every weak derivative of zero is zero (BB Def. 2.1, p. 68). -/
theorem hasWeakWordDeriv_zero (I : List (Fin m)) :
    hasWeakWordDeriv X Ω I (fun _ => 0) (fun _ => 0) := by
  refine ⟨?_, ?_, fun _ => by simp⟩ <;>
    exact continuousOn_const.locallyIntegrableOn Ω.isOpen.measurableSet

/-- Finite lists of weak derivatives can be summed (BB Def. 2.1, p. 68). -/
theorem hasWeakWordDeriv_list_sum {α : Type*}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (l : List α) (f g : α → (Fin n → ℝ) → ℝ)
    (h : ∀ a ∈ l, hasWeakWordDeriv X Ω I (f a) (g a)) :
    hasWeakWordDeriv X Ω I (fun x => (l.map (fun a => f a x)).sum)
      (fun x => (l.map (fun a => g a x)).sum) := by
  induction l with
  | nil => simpa using hasWeakWordDeriv_zero X Ω I
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simpa only [List.map_cons, List.sum_cons] using hasWeakWordDeriv_add X Ω hX ha hl

/-- Weak words are invariant under changing representatives on null sets
(BB Def. 2.1, p. 68). -/
theorem hasWeakWordDeriv_congr_ae {I : List (Fin m)} {f g f' g' : (Fin n → ℝ) → ℝ}
    (h : hasWeakWordDeriv X Ω I f g)
    (hf : f =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] f')
    (hg : g =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] g') :
    hasWeakWordDeriv X Ω I f' g' := by
  refine ⟨h.1.congr hf, h.2.1.congr hg, fun φ => ?_⟩
  calc
    (∫ x in (Ω : Set (Fin n → ℝ)), g' x * φ x) =
        ∫ x in (Ω : Set (Fin n → ℝ)), g x * φ x :=
      integral_congr_ae (hg.symm.mul ae_eq_rfl)
    _ = ∫ x in (Ω : Set (Fin n → ℝ)), f x * wordTranspose X I φ x := h.2.2 φ
    _ = ∫ x in (Ω : Set (Fin n → ℝ)), f' x * wordTranspose X I φ x :=
      integral_congr_ae (hf.mul ae_eq_rfl)

/-- Weak word derivatives vanish on every open patch where the original
function vanishes almost everywhere (BB p. 68; locality). -/
theorem hasWeakWordDeriv_locality (U : Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    {I : List (Fin m)} {f g : (Fin n → ℝ) → ℝ}
    (h : hasWeakWordDeriv X Ω I f g)
    (hf : f =ᵐ[volume.restrict (U : Set (Fin n → ℝ))] (fun _ => 0)) :
    g =ᵐ[volume.restrict (U : Set (Fin n → ℝ))] (fun _ => 0) := by
  have hu := hasWeakWordDeriv_restrict X Ω U hU h
  have hz := hasWeakWordDeriv_congr_ae X U hu hf ae_eq_rfl
  exact hasWeakWordDeriv_unique X U hz (hasWeakWordDeriv_zero X U I)

end RothschildStein.S

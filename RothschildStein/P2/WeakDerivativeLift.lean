-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FiberTest
public import RothschildStein.S.WeakDeriv
public import RothschildStein.Definitions.hasWeakWordDeriv

/-!
# Lifting weak derivatives

If `u` has the weak word derivative `g` on `Vo`, then the lift `u ∘ π` has the weak word
derivative `g ∘ π` for the triangular lift `X̃` on a lifted open set `Uo` (BB pp. 584–585, Thms
11.40–11.41), without any smoothness of `u`. The proof integrates tests over the fibers:
`A (X̃ᵢ^* φ) = Xᵢ^* (A φ)`, because the vertical divergences integrate to zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2
variable {n m k : ℕ}

theorem contDiff_basePoint : ContDiff ℝ (⊤ : ℕ∞) (basePoint : (Fin (n + m) → ℝ) → Fin n → ℝ) :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _

namespace FiberSetting

variable {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)} (S : FiberSetting Uo Vo)
include S

theorem contDiffOn_comp_basePoint {a : (Fin n → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Vo : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => a (basePoint ξ)) (Uo : Set (Fin (n + m) → ℝ)) :=
  ha.comp contDiff_basePoint.contDiffOn S.proj

/-- `A (X̃ᵢ^* φ) = Xᵢ^* (A φ)`: the fiber integral intertwines the transposes of a triangular
lift (the vertical divergences integrate to zero). -/
theorem test_fieldTransposeTest (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ))) (i : Fin k)
    (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    S.test (fieldTransposeTest Uo (triangularLift X P i) (hXt i) φ) =
      fieldTransposeTest Vo (X i) (hX i) (S.test φ) := by
  unfold fieldTransposeTest
  change S.testLM (-∑ j : Fin (n + m), _) = -∑ j : Fin n, _
  rw [map_neg, map_sum, Fin.sum_univ_add]
  congr 1
  have h1 : ∀ l : Fin m, ∀ ψ : TestFunction Uo ℝ (⊤ : ℕ∞),
      S.testLM (TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec (Fin.natAdd n l)) ψ) = 0 :=
    fun l ψ => S.test_lineDeriv_natAdd ψ l
  simp only [h1, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [testLM_apply, S.test_lineDeriv_castAdd]
  congr 1
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => (fun x => X i x j) (basePoint ξ))
      (Uo : Set (Fin (n + m) → ℝ)) :=
    S.contDiffOn_comp_basePoint ((contDiff_apply ℝ ℝ j).comp_contDiffOn (hX i))
  have hmul : testMultiplierOn Uo (fun x => triangularLift X P i x (Fin.castAdd m j))
      ((contDiff_apply ℝ ℝ (Fin.castAdd m j)).comp_contDiffOn (hXt i)) φ =
      testMultiplierOn Uo (fun ξ => (fun x => X i x j) (basePoint ξ)) hb φ := by
    apply TestFunction.ext
    intro ξ
    change φ ξ * triangularLift X P i ξ (Fin.castAdd m j) = φ ξ * X i (basePoint ξ) j
    simp [triangularLift]
  rw [hmul, S.test_multiplier_base (fun x => X i x j) _ hb]

/-- `A (X̃_I^* φ) = X_I^* (A φ)` for every word `I`. -/
theorem test_wordTransposeTest (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ))) (I : List (Fin k))
    (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    S.test (wordTransposeTest Uo (triangularLift X P) hXt I φ) =
      wordTransposeTest Vo X hX I (S.test φ) := by
  induction I generalizing φ with
  | nil => rfl
  | cons i I ih =>
    rw [wordTransposeTest, wordTransposeTest, ih, S.test_fieldTransposeTest X P hXt hX i]

/-- A function locally integrable on `Vo` lifts to a function locally integrable on `Uo`. -/
theorem locallyIntegrableOn_comp_basePoint {f : (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f (Vo : Set (Fin n → ℝ)) volume) :
    LocallyIntegrableOn (fun ξ => f (basePoint ξ)) (Uo : Set (Fin (n + m) → ℝ)) volume := by
  obtain ⟨c, hc0, hc⟩ := S.bounded
  rw [locallyIntegrableOn_iff Uo.isOpen.isLocallyClosed]
  intro K hKU hK
  have hπK : IsCompact (basePoint '' K) := hK.image continuous_basePoint
  have hπV : basePoint '' K ⊆ (Vo : Set (Fin n → ℝ)) := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact S.proj ξ (hKU hξ)
  have hfK : IntegrableOn f (basePoint '' K) volume := hf.integrableOn_compact_subset hπV hπK
  have hFB : FiberBounds K (basePoint '' K) ∅ c 0 :=
    { cup_nonneg := hc0
      clow_nonneg := le_rfl
      measurableSet_A := hK.measurableSet
      measurableSet_V := hπK.measurableSet
      measurableSet_W := MeasurableSet.empty
      subset := empty_subset _
      proj := fun ξ hξ => ⟨ξ, hξ, rfl⟩
      upper := fun z =>
        (show fiberVolume K z ≤ fiberVolume (Uo : Set (Fin (n + m) → ℝ)) z from
          measure_mono (fun t ht => hKU ht)).trans (hc z)
      lower := fun z hz => absurd hz (notMem_empty z) }
  refine ⟨aestronglyMeasurable_comp_basePoint hK.measurableSet hπK.measurableSet
    hFB.proj hfK.aestronglyMeasurable, ?_⟩
  have hle := hFB.lintegral_le (F := fun x => ‖f x‖ₑ) hfK.aestronglyMeasurable.enorm
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfK.2)

/-- Fubini on the fibers: `∫_{Uo} (f ∘ π) ψ = ∫_{Vo} f · A ψ`. -/
theorem integral_comp_mul_test {f : (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f (Vo : Set (Fin n → ℝ)) volume)
    (ψ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    (∫ ξ in (Uo : Set (Fin (n + m) → ℝ)), f (basePoint ξ) * ψ ξ) =
      ∫ x in (Vo : Set (Fin n → ℝ)), f x * S.test ψ x := by
  have hint := RothschildStein.S.integrable_mul_test Uo (S.locallyIntegrableOn_comp_basePoint hf) ψ
  have hz : ∀ ξ, ξ ∉ (Uo : Set (Fin (n + m) → ℝ)) → f (basePoint ξ) * ψ ξ = 0 := by
    intro ξ hξ
    simp [ψ.zero_on_compl hξ]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hz' : ∀ x, x ∉ (Vo : Set (Fin n → ℝ)) → f x * S.test ψ x = 0 := by
    intro x hx
    simp [(S.test ψ).zero_on_compl hx]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz']
  rw [← (measurePreserving_joinEquiv (n := n) (m := m)).integral_comp'
    (f := (joinEquiv n m)) (g := fun ξ => f (basePoint ξ) * ψ ξ)]
  have hint' : Integrable (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
      f (basePoint (joinEquiv n m p)) * ψ (joinEquiv n m p)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (measurePreserving_joinEquiv.integrable_comp_emb
      (joinEquiv n m).measurableEmbedding).2 hint
  rw [Measure.volume_eq_prod, integral_prod _ hint']
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  dsimp only
  simp_rw [joinEquiv_apply, basePoint_joinPoint]
  rw [integral_const_mul]
  rfl

/-- A weak word derivative of `u` on `Vo` lifts to a weak word
derivative of `u ∘ π` on `Uo` for the triangular lift (BB pp. 584–585, Thms 11.40–11.41). -/
theorem hasWeakWordDeriv_lift (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ))) (I : List (Fin k))
    {u g : (Fin n → ℝ) → ℝ} (h : hasWeakWordDeriv X Vo I u g) :
    hasWeakWordDeriv (triangularLift X P) Uo I (fun ξ => u (basePoint ξ))
      (fun ξ => g (basePoint ξ)) := by
  refine ⟨S.locallyIntegrableOn_comp_basePoint h.1, S.locallyIntegrableOn_comp_basePoint h.2.1,
    fun φ => ?_⟩
  rw [S.integral_comp_mul_test h.2.1 φ]
  have h2 := h.2.2 (S.test φ)
  rw [h2]
  have hc : ∀ x, wordTranspose X I (S.test φ) x =
      S.test (wordTransposeTest Uo (triangularLift X P) hXt I φ) x := by
    intro x
    rw [S.test_wordTransposeTest X P hXt hX I φ]
    exact (congrFun (RothschildStein.S.wordTransposeTest_apply Vo X hX I (S.test φ)) x).symm
  simp_rw [hc]
  rw [← S.integral_comp_mul_test h.1 (wordTransposeTest Uo (triangularLift X P) hXt I φ)]
  apply integral_congr_ae
  refine Eventually.of_forall fun ξ => ?_
  dsimp only
  rw [congrFun (RothschildStein.S.wordTransposeTest_apply Uo (triangularLift X P) hXt I φ) ξ]

end FiberSetting

end RothschildStein.P2

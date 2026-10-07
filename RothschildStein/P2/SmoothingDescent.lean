-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingCylinder
public import RothschildStein.P2.SmoothingChart
public import RothschildStein.Definitions.representsDistribution

/-!
# Distributional smoothing, descent: vertical constancy, tensor tests and descent to the base

Let `A ⊆ ℝⁿ`, `B ⊆ ℝᵐ` be open, `S` the fiber setting of the cylinder `A × B` over `A`, `η ∈ C_c^∞(B)`
with `∫ η = 1`, and `T` a distribution on `A` whose lift `T̃(ψ) = T(Jψ)` to the cylinder is
represented by a locally integrable `w` (BB p. 609). Then (`descent_of_lift`)

* `T(φ) = T̃(φ ⊗ η) = ∫ ū φ` with `ū(x) = ∫ w(x, t) η(t) dt` (tensor tests, Fubini), and
* `w(x, t) = ū(x)` a.e. on the cylinder, i.e. `w` is the lift of `ū` (the lift is vertically
  constant; `Distribution.ofFun_injective`).

For every word `I`, a locally integrable `g` representing the lifted derivative `X̃_I T̃` (that is, a
weak derivative of `w`) descends the same way: `X_I ū = ḡ` weakly on `A` (`hasWeakWordDeriv_descent`),
so `L^p` representatives of lifted derivatives average to `L^p` representatives of the base ones
(`memLp_fiberAvg`), and continuous representatives are independent of the vertical variable
(`eq_slice_of_continuousOn`, `fiberAvg_eq_slice`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2
variable {n m : ℕ}

namespace FiberSetting

variable {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)} (S : FiberSetting Uo Vo)
include S

/-- `ofFun f` evaluated on the fiber integral of `ψ` is `ofFun (f ∘ π)` evaluated on `ψ`. -/
theorem ofFun_test {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrableOn f (Vo : Set (Fin n → ℝ)) volume)
    (ψ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    Distribution.ofFun Vo f volume (⊤ : ℕ∞) (S.test ψ) =
      Distribution.ofFun Uo (fun ξ => f (basePoint ξ)) volume (⊤ : ℕ∞) ψ := by
  rw [ofFun_apply_eq_setIntegral Vo hf,
    ofFun_apply_eq_setIntegral Uo (S.locallyIntegrableOn_comp_basePoint hf)]
  exact (S.integral_comp_mul_test hf ψ).symm

end FiberSetting

section Descent

variable {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}

/-- Vertical constancy and descent: if the lift `T̃ = T ∘ J` of a distribution `T`
on `A` to the cylinder `A × B` is represented by a locally integrable `w`, then `T` is represented
by the vertical average `ū(x) = ∫ w(x, t) η(t) dt` and `w = ū ∘ π` almost everywhere on the cylinder
(BB p. 609, descent step of the distributional smoothing theorem; tensor tests `T(φ) = T̃(φ ⊗ η) = ∫ ū φ`). -/
theorem descent_of_lift (S : FiberSetting (cylinder A B) A) {η : TestFunction B ℝ (⊤ : ℕ∞)}
    (hη : ∫ t : Fin m → ℝ, η t = 1) (T : Distribution A ℝ (⊤ : ℕ∞))
    {w : (Fin (n + m) → ℝ) → ℝ}
    (hw : LocallyIntegrableOn w (cylinder A B : Set (Fin (n + m) → ℝ)) volume)
    (hT : ∀ ψ : TestFunction (cylinder A B) ℝ (⊤ : ℕ∞),
      T (S.test ψ) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) ψ) :
    representsDistribution A T (fiberAvg w η) ∧
      w =ᵐ[volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ))]
        fun ξ => fiberAvg w η (basePoint ξ) := by
  have hu := locallyIntegrableOn_fiberAvg hw η
  have hTu : T = Distribution.ofFun A (fiberAvg w η) volume (⊤ : ℕ∞) := by
    ext φ
    have h1 : T φ = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) (tensorTest φ η) := by
      rw [← hT, S.test_tensorTest_of_integral_eq_one φ hη]
    rw [h1, Distribution.ofFun_apply hw, Distribution.ofFun_apply hu]
    simp only [smul_eq_mul]
    exact integral_tensorTest_smul hw φ η
  refine ⟨⟨hu, hTu⟩, ?_⟩
  have hπu := S.locallyIntegrableOn_comp_basePoint hu
  have hinj : Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) =
      Distribution.ofFun (cylinder A B) (fun ξ => fiberAvg w η (basePoint ξ)) volume (⊤ : ℕ∞) := by
    ext ψ
    rw [← hT, hTu, S.ofFun_test hu]
  exact Distribution.ofFun_injective hw hπu hinj

/-- The words `X̃_I` of the lifted fields: if the lifted derivative `X̃_I T̃` is
represented by a locally integrable `g` (a weak derivative `X̃_I w = g`), then `g` is the lift of the
average `ḡ` and `ḡ` is the weak derivative `X_I ū` of the descended function (BB p. 609: each lifted
derivative distribution equals the lift of `X_I T`, by the first-order adjoint argument). -/
theorem hasWeakWordDeriv_descent {k : ℕ} (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i)
      (cylinder A B : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (A : Set (Fin n → ℝ)))
    (S : FiberSetting (cylinder A B) A) {η : TestFunction B ℝ (⊤ : ℕ∞)}
    (hη : ∫ t : Fin m → ℝ, η t = 1) (T : Distribution A ℝ (⊤ : ℕ∞))
    {w : (Fin (n + m) → ℝ) → ℝ}
    (hw : LocallyIntegrableOn w (cylinder A B : Set (Fin (n + m) → ℝ)) volume)
    (hT : ∀ ψ : TestFunction (cylinder A B) ℝ (⊤ : ℕ∞),
      T (S.test ψ) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) ψ)
    (I : List (Fin k)) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : hasWeakWordDeriv (triangularLift X P) (cylinder A B) I w g) :
    hasWeakWordDeriv X A I (fiberAvg w η) (fiberAvg g η) ∧
      g =ᵐ[volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ))]
        fun ξ => fiberAvg g η (basePoint ξ) := by
  have hdw : RothschildStein.S.distributionWordCLM (cylinder A B) (triangularLift X P) hXt I
      (Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞)) =
      Distribution.ofFun (cylinder A B) g volume (⊤ : ℕ∞) :=
    RothschildStein.S.distributionWord_ofFun_eq (cylinder A B) (triangularLift X P) hXt I w g hg
  have hSig : ∀ ψ : TestFunction (cylinder A B) ℝ (⊤ : ℕ∞),
      RothschildStein.S.distributionWordCLM A X hX I T (S.test ψ) =
        Distribution.ofFun (cylinder A B) g volume (⊤ : ℕ∞) ψ := by
    intro ψ
    rw [← hdw, RothschildStein.S.distributionWordCLM_apply, RothschildStein.S.distributionWordCLM_apply,
      ← S.test_wordTransposeTest X P hXt hX I ψ, hT]
  obtain ⟨hrepW, -⟩ := descent_of_lift S hη T hw hT
  obtain ⟨hrepG, hgae⟩ := descent_of_lift S hη _ hg.2.1 hSig
  refine ⟨?_, hgae⟩
  refine ⟨hrepW.1, hrepG.1, fun φ => ?_⟩
  have h1 : RothschildStein.S.distributionWordCLM A X hX I
      (Distribution.ofFun A (fiberAvg w η) volume (⊤ : ℕ∞)) =
      Distribution.ofFun A (fiberAvg g η) volume (⊤ : ℕ∞) := by
    rw [← hrepW.2, ← hrepG.2]
  have h2 := congrArg (fun D : Distribution A ℝ (⊤ : ℕ∞) => D φ) h1
  simp only [RothschildStein.S.distributionWordCLM_apply] at h2
  rw [ofFun_apply_eq_setIntegral A hrepW.1, ofFun_apply_eq_setIntegral A hrepG.1] at h2
  have h3 : ∀ x, (wordTransposeTest A X hX I φ : (Fin n → ℝ) → ℝ) x = wordTranspose X I φ x :=
    fun x => congrFun (RothschildStein.S.wordTransposeTest_apply A X hX I φ) x
  simp_rw [h3] at h2
  exact h2.symm

end Descent

end RothschildStein.P2

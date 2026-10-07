-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FiberIntegral
public import RothschildStein.P2.NormTransferLp
public import RothschildStein.Definitions.triangularLift
public import RothschildStein.Definitions.wordTransposeTest
public import RothschildStein.Definitions.testMultiplierOn
public import RothschildStein.S.Transposes

/-!
# Fiber integration of test functions

`FiberSetting Uo Vo` records what is used of a lifted open set `Uo` over a base open set `Vo`:
`π (Uo) ⊆ Vo`, bounded fiber volumes, and smoothness of the fiber integral of every test function
(the `fiber_average` field of the lifted chart). The fiber integral `A φ (x) = ∫ φ(x, t) dt` is a
linear map of test functions `D(Uo) → D(Vo)` (BB p. 584), commuting with the transposes of
the triangular lift: `A (X̃ᵢ^* φ) = Xᵢ^* (A φ)`, because the vertical divergences integrate to zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2
variable {n m : ℕ}

/-- The fiber setting of a lifted open set `Uo` over `Vo`. -/
structure FiberSetting (Uo : Opens (Fin (n + m) → ℝ)) (Vo : Opens (Fin n → ℝ)) : Prop where
  proj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ))
  bounded : ∃ c : ℝ, 0 ≤ c ∧ ∀ z, fiberVolume (Uo : Set (Fin (n + m) → ℝ)) z ≤ ENNReal.ofReal c
  smooth : ∀ φ : TestFunction Uo ℝ (⊤ : ℕ∞),
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => ∫ t : Fin m → ℝ, φ (joinPoint x t))


theorem integrable_slice {Uo : Opens (Fin (n + m) → ℝ)} (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) (x : Fin n → ℝ) :
    Integrable (fun t : Fin m → ℝ => φ (joinPoint x t)) :=
  (φ.continuous.comp (continuous_joinPoint_right x)).integrable_of_hasCompactSupport
    (hasCompactSupport_slice φ.hasCompactSupport x)

theorem fiber_eq_zero {Uo : Opens (Fin (n + m) → ℝ)} (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) (x : Fin n → ℝ)
    (hx : x ∉ basePoint '' tsupport (φ : (Fin (n + m) → ℝ) → ℝ)) :
    ∫ t : Fin m → ℝ, φ (joinPoint x t) = 0 := by
  have : ∀ t : Fin m → ℝ, φ (joinPoint x t) = 0 := by
    intro t
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hx ⟨_, hmem, basePoint_joinPoint x t⟩
  simp [this]

theorem natAdd_ne_castAdd (l : Fin m) (j : Fin n) : Fin.natAdd n l ≠ Fin.castAdd m j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  have := j.isLt
  omega

theorem baseDir_basisVec (j : Fin n) :
    baseDir (m := m) (Hormander.Interface.basisVec j) =
      Hormander.Interface.basisVec (Fin.castAdd m j) := by
  funext i
  refine Fin.addCases (fun j' => ?_) (fun l => ?_) i
  · simp [baseDir, joinPoint, Hormander.Interface.basisVec, Pi.single_apply]
  · simp [baseDir, joinPoint, Hormander.Interface.basisVec, Pi.single_apply]
    exact natAdd_ne_castAdd _ _

theorem vertDir_basisVec (l : Fin m) :
    vertDir (n := n) (Hormander.Interface.basisVec l) =
      Hormander.Interface.basisVec (Fin.natAdd n l) := by
  funext i
  refine Fin.addCases (fun j' => ?_) (fun l' => ?_) i
  · simp [vertDir, joinPoint, Hormander.Interface.basisVec, Pi.single_apply]
    exact (natAdd_ne_castAdd _ _).symm
  · simp [vertDir, joinPoint, Hormander.Interface.basisVec, Pi.single_apply]


namespace FiberSetting

variable {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)} (S : FiberSetting Uo Vo)
include S

/-- The fiber integral `A φ (x) = ∫ φ(x, t) dt` of a test function, as a test function on `Vo`. -/
def test (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) : TestFunction Vo ℝ (⊤ : ℕ∞) := by
  refine ⟨fun x => ∫ t : Fin m → ℝ, φ (joinPoint x t), S.smooth φ, ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_basePoint_image φ.hasCompactSupport)
      (fun x hx => fiber_eq_zero φ x hx)
  · have hsub : Function.support (fun x : Fin n → ℝ => ∫ t : Fin m → ℝ, φ (joinPoint x t)) ⊆
        basePoint '' tsupport (φ : (Fin (n + m) → ℝ) → ℝ) := by
      intro x hx
      by_contra h
      exact hx (fiber_eq_zero φ x h)
    refine (closure_minimal hsub (isCompact_basePoint_image φ.hasCompactSupport).isClosed).trans ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    exact S.proj ξ (φ.tsupport_subset hξ)

theorem test_apply (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) (x : Fin n → ℝ) :
    S.test φ x = ∫ t : Fin m → ℝ, φ (joinPoint x t) := rfl

/-- The fiber integral is linear. -/
def testLM : TestFunction Uo ℝ (⊤ : ℕ∞) →ₗ[ℝ] TestFunction Vo ℝ (⊤ : ℕ∞) where
  toFun := S.test
  map_add' φ ψ := by
    apply TestFunction.ext
    intro x
    change ∫ t : Fin m → ℝ, (φ (joinPoint x t) + ψ (joinPoint x t)) = _ + _
    exact integral_add (integrable_slice φ x) (integrable_slice ψ x)
  map_smul' c φ := by
    apply TestFunction.ext
    intro x
    change ∫ t : Fin m → ℝ, c * φ (joinPoint x t) = c * _
    exact integral_const_mul _ _

theorem testLM_apply (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) : S.testLM φ = S.test φ := rfl

/-- Base derivatives commute with the fiber integral. -/
theorem test_lineDeriv_castAdd (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) (j : Fin n) :
    S.test (TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec (Fin.castAdd m j)) φ) =
      TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec j) (S.test φ) := by
  apply TestFunction.ext
  intro x
  have hdiff : Differentiable ℝ (φ : (Fin (n + m) → ℝ) → ℝ) := φ.contDiff.differentiable (by simp)
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp), S.test_apply]
  change _ = lineDeriv ℝ (fun y : Fin n → ℝ => ∫ t : Fin m → ℝ, φ (joinPoint y t)) x _
  rw [lineDeriv_fiberAvg φ.contDiff φ.hasCompactSupport, baseDir_basisVec]
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  dsimp only
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (hdiff _).lineDeriv_eq_fderiv

/-- Vertical derivatives integrate to zero over the fiber. -/
theorem test_lineDeriv_natAdd (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) (l : Fin m) :
    S.test (TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec (Fin.natAdd n l)) φ) = 0 := by
  apply TestFunction.ext
  intro x
  have hdiff : Differentiable ℝ (φ : (Fin (n + m) → ℝ) → ℝ) := φ.contDiff.differentiable (by simp)
  rw [S.test_apply]
  change _ = (0 : ℝ)
  rw [← integral_fderiv_vertical (n := n) φ.contDiff φ.hasCompactSupport x
    (Hormander.Interface.basisVec l), vertDir_basisVec]
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  dsimp only
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (hdiff _).lineDeriv_eq_fderiv

/-- The fiber integral of a test function multiplied by a function of the base point. -/
theorem test_multiplier_base (a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Vo : Set (Fin n → ℝ)))
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => a (basePoint ξ)) (Uo : Set (Fin (n + m) → ℝ)))
    (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    S.test (testMultiplierOn Uo (fun ξ => a (basePoint ξ)) hb φ) =
      testMultiplierOn Vo a ha (S.test φ) := by
  apply TestFunction.ext
  intro x
  change ∫ t : Fin m → ℝ, φ (joinPoint x t) * a (basePoint (joinPoint x t)) =
    (∫ t : Fin m → ℝ, φ (joinPoint x t)) * a x
  simp_rw [basePoint_joinPoint]
  exact integral_mul_const _ _

end FiberSetting

end RothschildStein.P2

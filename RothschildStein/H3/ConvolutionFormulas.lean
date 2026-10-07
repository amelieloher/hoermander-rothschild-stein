-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalSecondTypeZero
public import RothschildStein.H1.KernelPotential
public import RothschildStein.H1.GaugeCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped BigOperators

/-- Convolution formulas for the fundamental kernel use one fixed finite
family of correction coefficients. Each equality follows from the kernel
hypotheses; no representation formula is assumed. -/
theorem convolution_formulas_of_fundamental_kernel {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ)) :
    ∃ c : Fin q → Fin q → ℝ,
      (∀ i j : Fin q, TypeZero G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))) ∧
      ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ContDiff ℝ (⊤ : ℕ∞) (G2.groupConvolution G φ K) ∧
        sumSquaresWithDrift H.fields (G2.groupConvolution G φ K) = φ ∧
        G2.groupConvolution G (sumSquaresWithDrift H.fields φ) K = φ ∧
        (∀ j : Fin q, fieldDerivative (H.fields j.succ) (G2.groupConvolution G φ K) =
          G2.groupConvolution G φ (fieldDerivative (H.fields j.succ) K)) ∧
        (∀ i j : Fin q,
          fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) (G2.groupConvolution G φ K)) =
            fun x => H1.principalValueConvolution G H.norm
              (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) φ x+c i j*φ x) ∧
        (∀ x, fieldDerivative (H.fields 0) (G2.groupConvolution G φ K) x = φ x-
          ∑ i : Fin q, fieldDerivative (H.fields i.succ)
            (fieldDerivative (H.fields i.succ) (G2.groupConvolution G φ K)) x) ∧
        (∀ j : Fin q, fieldDerivative (H.fields j.succ) φ =
          G2.groupConvolution G (sumSquaresWithDrift H.fields φ) (fieldDerivative (H.fields j.succ) K)) ∧
        (∀ i j : Fin q, fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) φ) =
          fun x => H1.principalValueConvolution G H.norm
            (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
            (sumSquaresWithDrift H.fields φ) x+c i j*sumSquaresWithDrift H.fields φ x) := by
  obtain ⟨η,R,hη,hsη,heη,hR,hout,hbη⟩ := H1.exists_compactGaugeCutoff G H.norm.gauge
  let c := fun i j : Fin q => ∫ z in {z | H.norm z ≤ R}, fieldDerivative (H.fields i.succ)
    (fun y => fieldDerivative (H.fields j.succ) K y*(1-η y)) z
  refine ⟨c, fun i j => fundamental_second_typeZero G H K i j, ?_⟩
  intro φ hφ hsφ
  let ψ : TestFunction (⊤ : Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞) := ⟨φ,hφ,hsφ,subset_univ _⟩
  have hconv : G2.groupConvolution G φ K = G.potential K ψ := by
    funext x
    rw [G2.groupConvolution_eq_integral]
    rfl
  have hfirst : ∀ j : Fin q, fieldDerivative (H.fields j.succ) (G2.groupConvolution G φ K) =
      G2.groupConvolution G φ (fieldDerivative (H.fields j.succ) K) := by
    intro j
    exact H.fieldDerivative_homogeneousPotential G j (K.smooth_off_zero.of_le (by simp))
      K.homogeneous (by linarith) hφ hsφ
  have heq : sumSquaresWithDrift H.fields (G2.groupConvolution G φ K) = φ := by
    rw [hconv]
    exact K.potential_equation ψ
  refine ⟨?_, heq, ?_, hfirst, ?_, ?_, ?_, ?_⟩
  · rw [hconv]
    exact K.potential_smooth ψ
  · funext x
    rw [G2.groupConvolution_eq_integral]
    exact (K.potential_twoSided hQ ψ x).2.symm
  · intro i j
    rw [hfirst j]
    obtain ⟨hf,hh⟩ := H.firstKernel_C1 G j (K.smooth_off_zero.of_le (by simp)) K.homogeneous
    simpa only [c, mul_comm] using H.fieldDerivative_criticalPotential_ballCoefficient G i hf hh
      hη hsη heη hR hout hbη hφ hsφ
  · intro x
    have hh := congrFun heq x
    change fieldDerivative (H.fields 0) (G2.groupConvolution G φ K) x+
      ∑ i : Fin q, fieldDerivative (H.fields i.succ)
        (fieldDerivative (H.fields i.succ) (G2.groupConvolution G φ K)) x = φ x at hh
    linarith
  · intro j
    exact K.firstDerivative_representation G H hQ j hφ hsφ
  · intro i j
    simpa only [c, mul_comm] using
      K.secondDerivative_representation G H hQ i j hη hsη heη hR hout hbη hφ hsφ

end RothschildStein.H3

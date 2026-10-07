-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PuncturedOperatorHomogeneity
public import RothschildStein.H1.LocalFinitePartialPairing
public import RothschildStein.G2.OperatorInvariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H3
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Every fixed finite smooth operator preserves local smoothness. -/
theorem differentialOperator_contDiffOn (P : SmoothDifferentialOperator N)
    (U : Opens (Fin N → ℝ)) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (U : Set (Fin N → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (P.apply f) (U : Set (Fin N → ℝ)) := by
  apply contDiffOn_infty.mpr
  intro k
  unfold SmoothDifferentialOperator.apply
  apply ContDiffOn.sum
  intro a ha
  exact ((P.smooth_coefficient a ha).of_le (by simp)).contDiffOn.mul
    (H1.contDiffOn_euclideanPartial_finite U a k f (hf.of_le (by simp)))

/-- A degree-m finite operator lowers a punctured kernel's degree
by m, using the shared smooth-germ extension (BB Proposition 3.23, p. 107). -/
theorem homogeneousOperator_kernel (P : SmoothDifferentialOperator N)
    {m γ : ℝ} (hP : P.IsHomogeneous G m)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ γ * f x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (P.apply f) {0}ᶜ ∧
    ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      P.apply f (G.dilate t x) = t ^ (γ - m) * P.apply f x :=
  ⟨differentialOperator_contDiffOn P ⟨{0}ᶜ, isOpen_compl_singleton⟩ hf,
    fun _ ht _ hx => H1.differentialOperator_punctured_homogeneity G P hP hf hhom ht hx⟩

end RothschildStein.H3

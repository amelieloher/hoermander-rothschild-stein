-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantDivergence
public import RothschildStein.S.IntegrationByParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open Set MeasureTheory
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Integration by parts for left-invariant fields, with the second factor compactly
supported (BB (3.12), p. 110). -/
theorem integral_leftField_mul (v : Fin N → ℝ) (f g : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcg : HasCompactSupport g) :
    (∫ x, fieldDerivative (leftField G v) f x * g x) =
      -(∫ x, f x * fieldDerivative (leftField G v) g x) := by
  let φ : TestFunction (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
    ⟨g, hg, hcg, subset_univ _⟩
  have h := S.integral_fieldDerivative_mul_test ⊤ (leftField G v)
    (contDiff_leftField G v).contDiffOn f (hf.of_le (by simp)).contDiffOn φ
  have he : fieldTranspose (leftField G v) φ = -fieldDerivative (leftField G v) g := by
    funext x
    exact leftField_transpose G v g hg x
  have hc : (φ : (Fin N → ℝ) → ℝ) = g := rfl
  rw [he, hc] at h
  simpa only [TopologicalSpace.Opens.coe_top, setIntegral_univ, Pi.neg_apply,
    mul_neg, integral_neg] using h

end RothschildStein.G2

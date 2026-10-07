-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ParameterizedIncrement
public import RothschildStein.G2.AnalyticStructure
public import RothschildStein.G2.Algebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul

namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Right group increments have a uniform Euclidean
Lipschitz bound when a compact parameter cutoff is one. -/
theorem exists_rightGroup_increment_bound
    {ψ η : (Fin N → ℝ) → ℝ} (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ)
    (hcη : ContDiff ℝ 1 η) (hsη : HasCompactSupport η) (hη0 : η 0 = 1)
    {W : Set (Fin N → ℝ)} (hη : ∀ w ∈ W, η w = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x w, w ∈ W → |ψ (G.mul x w) - ψ x| ≤ C * ‖w‖ := by
  let F : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ) := fun p => G.mul p.1 p.2
  let I : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ) := fun p => G.mul p.1 (G.inv p.2)
  have hF : ContDiff ℝ 1 F := (G2.contDiff_mul G).of_le (by simp)
  have hI : Continuous I := (G2.continuous_mul G).comp
    (continuous_fst.prodMk ((G2.continuous_inv G).comp continuous_snd))
  have hInv (x w : Fin N → ℝ) : I (F (x, w), w) = x := by
    change G.mul (G.mul x w) (G.inv w) = x
    rw [G2.mul_assoc, G2.mul_inv, G2.mul_zero]
  have hZero (x : Fin N → ℝ) : F (x, 0) = x := G2.mul_zero G x
  have h := exists_parameterizedCompact_increment_bound (E := Fin N → ℝ) (F := F) (I := I) (ψ := ψ) (η := η)
    (W := W) hF hI hInv hZero hcψ hsψ hcη hsη hη0 hη
  simpa only [F] using h

/-- Left group increments have the corresponding uniform
Euclidean Lipschitz bound. -/
theorem exists_leftGroup_increment_bound
    {ψ η : (Fin N → ℝ) → ℝ} (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ)
    (hcη : ContDiff ℝ 1 η) (hsη : HasCompactSupport η) (hη0 : η 0 = 1)
    {W : Set (Fin N → ℝ)} (hη : ∀ w ∈ W, η w = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x w, w ∈ W → |ψ (G.mul w x) - ψ x| ≤ C * ‖w‖ := by
  let F : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ) := fun p => G.mul p.2 p.1
  let I : (Fin N → ℝ) × (Fin N → ℝ) → (Fin N → ℝ) := fun p => G.mul (G.inv p.2) p.1
  have hF : ContDiff ℝ 1 F :=
    ((G2.contDiff_mul G).comp (contDiff_snd.prodMk contDiff_fst)).of_le (by simp)
  have hI : Continuous I := (G2.continuous_mul G).comp
    (((G2.continuous_inv G).comp continuous_snd).prodMk continuous_fst)
  have hInv (x w : Fin N → ℝ) : I (F (x, w), w) = x := by
    change G.mul (G.inv w) (G.mul w x) = x
    rw [← G2.mul_assoc, G2.inv_mul, G2.zero_mul]
  have hZero (x : Fin N → ℝ) : F (x, 0) = x := G2.zero_mul G x
  have h := exists_parameterizedCompact_increment_bound (E := Fin N → ℝ) (F := F) (I := I) (ψ := ψ) (η := η)
    (W := W) hF hI hInv hZero hcψ hsψ hcη hsη hη0 hη
  simpa only [F] using h

end RothschildStein.H1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetProducts
public import RothschildStein.L1.WeightedJetAddition
public import RothschildStein.L1.WeightedJetLocality
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The actual directional derivative is the sum of actual coordinate derivatives. -/
theorem fieldDerivative_eq_coordinate_sum {N : ℕ}
    (R : (Fin N → ℝ) → (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    fieldDerivative R f x = ∑ j, R x j * rsPartial [j] f x := by
  have hv : (∑ j : Fin N, R x j • Pi.single j (1 : ℝ)) = R x := by
    ext i
    simp [Pi.single_apply]
  unfold fieldDerivative
  simpa only [map_sum, map_smul, smul_eq_mul, rsPartial] using
    (congrArg (fderiv ℝ f x) hv).symm

/-- A field of threshold a
acts on a scalar of threshold b with threshold a+b and loses one jet order. -/
theorem scalarJetClass_fieldDerivative {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {R : (Fin N → ℝ) → (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    (hR : fieldJetClass Ω ω a p R) (hf : scalarJetClass Ω ω b (p+1) f) :
    scalarJetClass Ω ω (a+b) p (fieldDerivative R f) := by
  have hs : scalarJetClass Ω ω (a+b) p
      (fun u => ∑ j : Fin N, R u j * rsPartial [j] f u) := by
    apply scalarJetClass_sum Ω h0 ω (a+b) Finset.univ
    intro j _
    have hr : scalarJetClass Ω ω (a + ω j) p (fun u => R u j) :=
      ⟨contDiffOn_pi.mp hR.1 j, hR.2 j⟩
    have hj := scalarJetClass_mul Ω h0 hr (scalarJetClass_partial Ω hf j)
    convert hj using 1; ring
  exact scalarJetClass_congr Ω h0 hs (fun u _ => fieldDerivative_eq_coordinate_sum R f u)

/-- A field vanishing at zero saves that ordinary jet order in its action. -/
theorem circleScalarJetClass_fieldDerivative {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {R : (Fin N → ℝ) → (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    (hR : circleFieldJetClass Ω ω a (p+1) R)
    (hf : scalarJetClass Ω ω b (p+1) f) :
    circleScalarJetClass Ω ω (a+b) (p+1) (fieldDerivative R f) := by
  refine ⟨?_, ?_⟩
  · have hs : scalarJetClass Ω ω (a+b) (p+1)
        (fun u => ∑ j : Fin N, R u j * rsPartial [j] f u) := by
      apply scalarJetClass_sum Ω h0 ω (a+b) Finset.univ
      intro j _
      have hr : scalarJetClass Ω ω (a + ω j) (p+1) (fun u => R u j) :=
        ⟨contDiffOn_pi.mp hR.1.1 j, hR.1.2 j⟩
      have hd := scalarJetClass_partial Ω hf j
      refine ⟨hr.1.mul hd.1, ?_⟩
      have hj := scalarJetVanishing_mul_of_zero Ω h0 hr.1 hd.1
        (by simp only [hR.2, Pi.zero_apply]) hr.2 hd.2
      convert hj using 1; ring
    exact scalarJetClass_congr Ω h0 hs (fun u _ => fieldDerivative_eq_coordinate_sum R f u)
  · simp only [fieldDerivative, hR.2, map_zero]
end RothschildStein.L1

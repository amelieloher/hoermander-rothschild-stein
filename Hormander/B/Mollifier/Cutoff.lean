-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.CutoffAlgebra

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem tsupport_complexifyRealSchwartz (z : SchwartzMap (Carrier N) ℝ) :
    tsupport (complexifyRealSchwartz z : Carrier N → ℂ) = tsupport (z : Carrier N → ℝ) := by
  have : Function.support (complexifyRealSchwartz z : Carrier N → ℂ) =
      Function.support (z : Carrier N → ℝ) := by
    ext y; simp [Function.mem_support, complexifyRealSchwartz_apply]
  unfold tsupport
  rw [this]

theorem vectorField_apply_eq_zero (X : RealSchwartzVectorField N) (g : TestFunction N)
    (x : Carrier N) (hx : x ∉ tsupport (g : Carrier N → ℂ)) : vectorFieldOperator X g x = 0 := by
  rw [vectorFieldOperator_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : coordinateDerivative i g x = 0 := by
    have hsub : tsupport ((coordinateDerivative i g : TestFunction N) : Carrier N → ℂ) ⊆
        tsupport (g : Carrier N → ℂ) :=
      SchwartzMap.tsupport_lineDerivOp_subset (EuclideanSpace.single i (1 : ℝ)) g
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))
  rw [h, mul_zero]

theorem tsupport_vectorField_subset (X : RealSchwartzVectorField N) (g : TestFunction N) :
    tsupport (vectorFieldOperator X g : Carrier N → ℂ) ⊆ tsupport (g : Carrier N → ℂ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxg
  exact hx (vectorField_apply_eq_zero X g x hxg)

/-- A multiplier is unchanged by an outer multiplier equal to one on the support of its
coefficient. -/
theorem multiplier_absorb_of_tsupport (g : TestFunction N) (z : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (g : Carrier N → ℂ), z x = 1) :
    (multiplierOperator g).comp (realMultiplierOperator z) = multiplierOperator g := by
  apply multiplierOperator_absorption
  intro x hx
  simp [complexifyRealSchwartz_apply, hz x hx]


theorem vectorField_leibniz_apply (X : RealSchwartzVectorField N) (g : TestFunction N)
    (w : TestFunction N) :
    vectorFieldOperator X (multiplierOperator g w) - multiplierOperator g (vectorFieldOperator X w) =
      multiplierOperator (vectorFieldOperator X g) w :=
  LinearMap.congr_fun (operatorComm_vectorField_multiplier X g) w

/-- Exact cutoff identity for the first commutator: the commutator with `S_δ ζ₁` is
`[S_δ,X] ζ₁ − S_δ (Xζ₁)`; it is unchanged by a right factor `ζ₂` which is one near the support
of `ζ₁`. No restriction on `δ`. -/
theorem mollifier_cutoff_identity_first (X : RealSchwartzVectorField N)
    (z1 z2 : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (z1 : Carrier N → ℝ), z2 x = 1) (δ : ℝ) (hδ : 0 < δ) :
    operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1)) (vectorFieldOperator X) =
        (operatorComm (mollOp N δ hδ) (vectorFieldOperator X)).comp (realMultiplierOperator z1) -
          (mollOp N δ hδ).comp (multiplierOperator
            (vectorFieldOperator X (complexifyRealSchwartz z1))) ∧
      operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1)) (vectorFieldOperator X) =
        (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
          (vectorFieldOperator X)).comp (realMultiplierOperator z2) := by
  have hid := comm_cutoff_identity (mollOp N δ hδ) (vectorFieldOperator X)
    (realMultiplierOperator z1) (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1)))
    (fun w => vectorField_leibniz_apply X (complexifyRealSchwartz z1) w)
  refine ⟨hid, ?_⟩
  have h1 : (realMultiplierOperator z1).comp (realMultiplierOperator z2) =
      realMultiplierOperator z1 :=
    multiplier_absorb_of_tsupport (complexifyRealSchwartz z1) z2 (by
      rw [tsupport_complexifyRealSchwartz]; exact hz)
  have h2 : (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1))).comp
      (realMultiplierOperator z2) =
      multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1)) :=
    multiplier_absorb_of_tsupport _ z2 (fun x hx => hz x (by
      rw [← tsupport_complexifyRealSchwartz]
      exact tsupport_vectorField_subset X _ hx))
  rw [hid, LinearMap.sub_comp, LinearMap.comp_assoc, h1, LinearMap.comp_assoc, h2]

/-- Exact cutoff identity for the double commutator, with the displayed expansion
`[[S ζ₁,X],X] = [[S,X],X] ζ₁ − 2 [S,X] (Xζ₁) + S (X²ζ₁)` and the right factorization through
`ζ₂`. No restriction on `δ`. -/
theorem mollifier_cutoff_identity_second (X : RealSchwartzVectorField N)
    (z1 z2 : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (z1 : Carrier N → ℝ), z2 x = 1) (δ : ℝ) (hδ : 0 < δ) :
    operatorComm (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
        (vectorFieldOperator X)) (vectorFieldOperator X) =
        (operatorComm (operatorComm (mollOp N δ hδ) (vectorFieldOperator X))
            (vectorFieldOperator X)).comp (realMultiplierOperator z1) -
          (2 : ℂ) • (operatorComm (mollOp N δ hδ) (vectorFieldOperator X)).comp
            (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1))) +
          (mollOp N δ hδ).comp (multiplierOperator
            (vectorFieldOperator X (vectorFieldOperator X (complexifyRealSchwartz z1)))) ∧
      operatorComm (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
        (vectorFieldOperator X)) (vectorFieldOperator X) =
        (operatorComm (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator z1))
          (vectorFieldOperator X)) (vectorFieldOperator X)).comp (realMultiplierOperator z2) := by
  have hid := comm2_cutoff_identity (mollOp N δ hδ) (vectorFieldOperator X)
    (realMultiplierOperator z1) (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1)))
    (multiplierOperator (vectorFieldOperator X (vectorFieldOperator X (complexifyRealSchwartz z1))))
    (fun w => vectorField_leibniz_apply X (complexifyRealSchwartz z1) w)
    (fun w => vectorField_leibniz_apply X (vectorFieldOperator X (complexifyRealSchwartz z1)) w)
  refine ⟨hid, ?_⟩
  have hsub1 : tsupport (vectorFieldOperator X (complexifyRealSchwartz z1) : Carrier N → ℂ) ⊆
      tsupport (z1 : Carrier N → ℝ) := by
    rw [← tsupport_complexifyRealSchwartz]; exact tsupport_vectorField_subset X _
  have h1 : (realMultiplierOperator z1).comp (realMultiplierOperator z2) =
      realMultiplierOperator z1 :=
    multiplier_absorb_of_tsupport (complexifyRealSchwartz z1) z2 (by
      rw [tsupport_complexifyRealSchwartz]; exact hz)
  have h2 : (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1))).comp
      (realMultiplierOperator z2) =
      multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1)) :=
    multiplier_absorb_of_tsupport _ z2 (fun x hx => hz x (hsub1 hx))
  have h3 : (multiplierOperator (vectorFieldOperator X (vectorFieldOperator X
      (complexifyRealSchwartz z1)))).comp (realMultiplierOperator z2) =
      multiplierOperator (vectorFieldOperator X (vectorFieldOperator X
        (complexifyRealSchwartz z1))) :=
    multiplier_absorb_of_tsupport _ z2 (fun x hx => hz x (hsub1
      ((tsupport_vectorField_subset X _) hx)))
  rw [hid, LinearMap.add_comp, LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_assoc,
    h1, LinearMap.comp_assoc, h2, LinearMap.comp_assoc, h3]

end Hormander.B

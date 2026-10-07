-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.CutoffBound
public import Hormander.B.Differential

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

/-- The one-step cutoff identity and right factorization for an arbitrary left factor `S`. -/
theorem cutoff_identity_first_gen (S : Operator N) (X : RealSchwartzVectorField N)
    (z1 z2 : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (z1 : Carrier N → ℝ), z2 x = 1) :
    operatorComm (S.comp (realMultiplierOperator z1)) (vectorFieldOperator X) =
        (operatorComm S (vectorFieldOperator X)).comp (realMultiplierOperator z1) -
          S.comp (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1))) ∧
      operatorComm (S.comp (realMultiplierOperator z1)) (vectorFieldOperator X) =
        (operatorComm (S.comp (realMultiplierOperator z1))
          (vectorFieldOperator X)).comp (realMultiplierOperator z2) := by
  have hid := comm_cutoff_identity S (vectorFieldOperator X)
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

/-- The two-step cutoff identity and right factorization for an arbitrary left factor `S`. -/
theorem cutoff_identity_second_gen (S : Operator N) (X : RealSchwartzVectorField N)
    (z1 z2 : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (z1 : Carrier N → ℝ), z2 x = 1) :
    operatorComm (operatorComm (S.comp (realMultiplierOperator z1)) (vectorFieldOperator X))
        (vectorFieldOperator X) =
        (operatorComm (operatorComm S (vectorFieldOperator X)) (vectorFieldOperator X)).comp
            (realMultiplierOperator z1) -
          (2 : ℂ) • (operatorComm S (vectorFieldOperator X)).comp
            (multiplierOperator (vectorFieldOperator X (complexifyRealSchwartz z1))) +
          S.comp (multiplierOperator
            (vectorFieldOperator X (vectorFieldOperator X (complexifyRealSchwartz z1)))) ∧
      operatorComm (operatorComm (S.comp (realMultiplierOperator z1)) (vectorFieldOperator X))
        (vectorFieldOperator X) =
        (operatorComm (operatorComm (S.comp (realMultiplierOperator z1))
          (vectorFieldOperator X)) (vectorFieldOperator X)).comp (realMultiplierOperator z2) := by
  have hid := comm2_cutoff_identity S (vectorFieldOperator X)
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

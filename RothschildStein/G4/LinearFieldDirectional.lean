-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LinearFieldDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- The spatial differential of the parameter-linear field is
the same linear combination of the field differentials
(BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_spatial_fderiv {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Fin m → E → E)
    (z : Fin m → ℝ) (x a : E) (hW : ∀ j, DifferentiableAt ℝ (W j) x) :
    fderiv ℝ (fun y => ∑ j, z j • W j y) x a = ∑ j, z j • fderiv ℝ (W j) x a := by
  have hd : HasFDerivAt (fun y => ∑ j, z j • W j y) (∑ j, z j • fderiv ℝ (W j) x) x :=
    HasFDerivAt.fun_sum (fun j _ => (hW j).hasFDerivAt.const_smul (z j))
  rw [hd.fderiv]
  simp only [sum_apply, smul_apply]

/-- A pure parameter-coordinate variation has forcing exactly
W_i, plus the spatial transport term DW_z·v
(BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_parameter_forcing {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Fin m → E → E)
    (z : Fin m → ℝ) (x v : E) (hW : ∀ j, DifferentiableAt ℝ (W j) x) (i : Fin m) :
    fderiv ℝ (fun q : (Fin m → ℝ) × E => ∑ j, q.1 j • W j q.2) (z, x) (Pi.single i 1, v) =
      fderiv ℝ (fun y => ∑ j, z j • W j y) x v + W i x := by
  classical
  rw [linear_field_family_fderiv W (z, x) (Pi.single i 1, v) hW,
    linear_field_spatial_fderiv W z x v hW, Finset.sum_add_distrib]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end RothschildStein.G4

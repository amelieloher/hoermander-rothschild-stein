-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetDerivatives
public import RothschildStein.L1.WeightedJetLocality
public import RothschildStein.G1.BracketAlgebra
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1

/-- Ordinary Euler operator on scalar coefficients, with BB's factor two. -/
def scalarJetEuler {N : ℕ} (f : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) : ℝ :=
  2 * f u + fieldDerivative id f u

/-- The scalar Euler expression remains smooth on the open domain. -/
theorem scalarJetEuler_contDiffOn {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (scalarJetEuler f) Ω :=
  (contDiffOn_const.mul hf).add (S.contDiffOn_fieldDerivative Ω id f contDiffOn_id hf)

set_option backward.defeqAttrib.useBackward true in
/-- A coordinate derivative commutes with the Euler operator up to
one copy of that derivative, from the actual bracket of id and a constant field. -/
theorem rsPartial_scalarJetEuler_single {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (j : Fin N) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    rsPartial [j] (scalarJetEuler f) x =
      scalarJetEuler (rsPartial [j] f) x + rsPartial [j] f x := by
  have hfD := S.contDiffOn_fieldDerivative Ω id f contDiffOn_id hf
  have hdf := (hf.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hdD := (hfD.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hbr := G1.bracket_derivative Ω.isOpen
    (U := fun _ => Pi.single j (1 : ℝ)) (V := id) contDiffOn_const contDiffOn_id hf hx
  have hb : VectorField.lieBracket ℝ (fun _ : Fin N → ℝ => Pi.single j 1) id =
      fun _ => Pi.single j 1 := by
    funext y
    simp only [VectorField.lieBracket, fderiv_id, fderiv_const_apply,
      ContinuousLinearMap.id_apply, zero_apply, sub_zero]
  rw [hb] at hbr
  change fderiv ℝ (fun y => 2 * f y + fieldDerivative id f y) x (Pi.single j 1) = _
  have hd2 : DifferentiableAt ℝ (fun y => (2 : ℝ) * f y) x := hdf.const_mul 2
  rw [fderiv_fun_add hd2 hdD, fderiv_const_mul hdf]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change 2 * rsPartial [j] f x +
    fieldDerivative (fun _ => Pi.single j 1) (fieldDerivative id f) x = _
  unfold scalarJetEuler
  change 2 * rsPartial [j] f x +
    fieldDerivative (fun _ => Pi.single j 1) (fieldDerivative id f) x =
    2 * rsPartial [j] f x + fieldDerivative id (rsPartial [j] f) x + rsPartial [j] f x
  change rsPartial [j] f x =
    fieldDerivative (fun _ => Pi.single j 1) (fieldDerivative id f) x -
      fieldDerivative id (rsPartial [j] f) x at hbr
  linarith
end RothschildStein.L1

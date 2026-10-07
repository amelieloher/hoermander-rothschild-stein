-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- The differential of the parameter-linear field has the
parameter forcing and spatial transport terms, with both Leibniz terms
retained (BB Lemma 9.48, pp. 441–442). -/
theorem linear_field_family_fderiv {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Fin m → E → E)
    (p a : (Fin m → ℝ) × E) (hW : ∀ j, DifferentiableAt ℝ (W j) p.2) :
    fderiv ℝ (fun q : (Fin m → ℝ) × E => ∑ j, q.1 j • W j q.2) p a =
      ∑ j, (p.1 j • fderiv ℝ (W j) p.2 a.2 + a.1 j • W j p.2) := by
  let D : ((Fin m → ℝ) × E) →L[ℝ] E := ∑ j,
    (p.1 j • ((fderiv ℝ (W j) p.2).comp (ContinuousLinearMap.snd ℝ (Fin m → ℝ) E)) +
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Fin m → ℝ) E)).smulRight (W j p.2))
  have hd : HasFDerivAt (fun q : (Fin m → ℝ) × E => ∑ j, q.1 j • W j q.2) D p := by
    dsimp only [D]
    apply HasFDerivAt.fun_sum
    intro j _
    exact ((ContinuousLinearMap.proj j).hasFDerivAt.comp p
      (ContinuousLinearMap.fst ℝ (Fin m → ℝ) E).hasFDerivAt).smul
      ((hW j).hasFDerivAt.comp p (ContinuousLinearMap.snd ℝ (Fin m → ℝ) E).hasFDerivAt)
  rw [hd.fderiv]
  simp only [D, sum_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ProfileDerivatives
public import RothschildStein.H3.SmoothGaugeCutoff
public import RothschildStein.Definitions.fieldDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
variable {N : ℕ}

/-- The scalar chain rule for one field action; this is the first
step of the noncommutative word induction on the punctured gauge domain. -/
theorem fieldDerivative_scalar_comp
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {F : ℝ → ℝ}
    {ν : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hF : DifferentiableAt ℝ F (ν x)) (hν : DifferentiableAt ℝ ν x) :
    fieldDerivative V (F ∘ ν) x = deriv F (ν x) * fieldDerivative V ν x := by
  unfold fieldDerivative
  rw [fderiv_comp x hF hν, ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]

/-- Exact first field derivative of the radial cutoff off the center. -/
theorem fieldDerivative_quasiballProfile (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (t s : ℝ)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    fieldDerivative V (quasiballProfile t s ∘ ν) x =
      deriv (quasiballProfile t s) (ν x) * fieldDerivative V ν x := by
  apply fieldDerivative_scalar_comp V
    ((quasiballProfile_contDiff t s).differentiable (by simp)).differentiableAt
  exact (hν.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialFieldChain
public import RothschildStein.S.Transposes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Filter
open scoped Topology
variable {N : ℕ}

/-- The second noncommutative radial chain rule on the punctured
domain. The ordered second field action is retained in the second term. -/
theorem fieldDerivative_second_scalar_comp
    (U V : (Fin N → ℝ) → (Fin N → ℝ)) {F : ℝ → ℝ}
    {ν : (Fin N → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) {x : Fin N → ℝ} (hx : x ≠ 0) :
    fieldDerivative U (fieldDerivative V (F ∘ ν)) x =
      deriv (deriv F) (ν x) * fieldDerivative U ν x * fieldDerivative V ν x +
      deriv F (ν x) * fieldDerivative U (fieldDerivative V ν) x := by
  have hdν : DifferentiableAt ℝ ν x :=
    (hν.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  have hdF : Differentiable ℝ (deriv F) :=
    (hF.of_le (by simp)).differentiable_deriv_two
  have hdVν : DifferentiableAt ℝ (fieldDerivative V ν) x :=
    ((S.contDiffOn_fieldDerivative ⟨{0}ᶜ, isOpen_compl_singleton⟩ V ν
      hV.contDiffOn hν).contDiffAt
      (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  have he : fieldDerivative V (F ∘ ν) =ᶠ[𝓝 x]
      (fun y => deriv F (ν y) * fieldDerivative V ν y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    apply fieldDerivative_scalar_comp V
      ((hF.differentiable (by simp)).differentiableAt)
    exact (hν.contDiffAt (isOpen_compl_singleton.mem_nhds hy)).differentiableAt (by simp)
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have hact : fieldDerivative U (fieldDerivative V (F ∘ ν)) x =
      fieldDerivative U (fun y => deriv F (ν y) * fieldDerivative V ν y) x :=
    congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (U x)) hd
  rw [hact]
  have hp := S.fieldDerivative_mul U (fun y => deriv F (ν y)) (fieldDerivative V ν) x
    (hdF.differentiableAt.comp x hdν) hdVν
  rw [hp]
  have hc := fieldDerivative_scalar_comp U hdF.differentiableAt hdν
  have hc' : fieldDerivative U (fun y => deriv F (ν y)) x =
      deriv (deriv F) (ν x) * fieldDerivative U ν x := by
    simpa only [Function.comp_def] using hc
  rw [hc']

end RothschildStein.H3

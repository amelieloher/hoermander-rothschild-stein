-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GeneratorTransferRemainder
public import RothschildStein.P1.KernelEstimatesChain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)
variable {Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ}

/-- Input chain rule for the actual parameter
family, with the model coordinate held fixed in the parameter term
(BB Theorem 11.24, pp. 555–558). -/
theorem hasFDerivAt_transfer_input_kernel
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    HasFDerivAt (fun ζ => Ψ ξ ζ (C.Θ ζ ξ))
      ((fderiv ℝ (kernelUncurry Ψ) (ξ, η, C.Θ η ξ)).comp
        ((0 : (Fin (n+m) → ℝ) →L[ℝ] (Fin (n+m) → ℝ)).prod
          ((ContinuousLinearMap.id ℝ (Fin (n+m) → ℝ)).prod
            (fderiv ℝ (fun ζ => C.Θ ζ ξ) η)))) η := by
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ => C.Θ ζ ξ) C.U :=
    C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hζ => ⟨hζ, hξ⟩)
  have hd : DifferentiableAt ℝ (fun ζ => C.Θ ζ ξ) η :=
    (hθ.differentiableOn (by simp)).differentiableAt (C.isOpen_U.mem_nhds hη)
  have hu := (C.theta_eq_zero_iff hη hξ).not.mpr hne
  exact (kernelUncurry_differentiableAt hΨ hu).hasFDerivAt.comp η
    ((hasFDerivAt_const ξ η).prodMk ((hasFDerivAt_id η).prodMk hd.hasFDerivAt))

/-- Transfer cancels every model derivative
except the complete weighted remainder. Both endpoint parameter
variations remain explicit (BB (11.36)–(11.37), pp. 555–556). -/
theorem transfer_kernel_chain_rule
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0}) (i : Fin k)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    fieldDerivative (C.Xl i) (fun ζ => Ψ ζ η (C.Θ η ζ)) ξ +
      ∑ j, MvPolynomial.eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) *
        fieldDerivative (wordBracket C.Xl (C.B j)) (fun ζ => Ψ ξ ζ (C.Θ ζ ξ)) η =
      fderiv ℝ (kernelUncurry Ψ) (ξ, η, C.Θ η ξ)
        (C.Xl i ξ, ∑ j, MvPolynomial.eval (C.Θ η ξ)
          (C.generatorTransferCoefficient i j) • wordBracket C.Xl (C.B j) η,
          C.generatorTransferRemainder i ξ η (C.Θ η ξ)) := by
  classical
  simp only [fieldDerivative]
  rw [(C.hasFDerivAt_kernel hΨ hη hξ hne).fderiv,
    (C.hasFDerivAt_transfer_input_kernel hΨ hξ hη hne).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply]
  simp_rw [← smul_eq_mul, ← map_smul]
  rw [← map_sum, ← map_add]
  simp only [Prod.smul_mk, smul_zero, ← prod_mk_sum, Finset.sum_const_zero,
    Prod.mk_add_mk, zero_add, add_zero]
  congr 1
  rw [C.generator_chart_transfer i hξ hη]
  abel_nf

/-- Split the transferred derivative into the
output parameter, input parameter, and full model remainder actions
(BB Theorem 11.24, pp. 555–558). -/
theorem transfer_kernel_chain_rule_split
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0}) (i : Fin k)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    fieldDerivative (C.Xl i) (fun ζ => Ψ ζ η (C.Θ η ζ)) ξ +
      ∑ j, MvPolynomial.eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) *
        fieldDerivative (wordBracket C.Xl (C.B j)) (fun ζ => Ψ ξ ζ (C.Θ ζ ξ)) η =
      fderiv ℝ (kernelUncurry Ψ) (ξ, η, C.Θ η ξ) (C.Xl i ξ, 0, 0) +
      (∑ j, MvPolynomial.eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) *
        fderiv ℝ (kernelUncurry Ψ) (ξ, η, C.Θ η ξ) (0, wordBracket C.Xl (C.B j) η, 0)) +
      fderiv ℝ (kernelUncurry Ψ) (ξ, η, C.Θ η ξ)
        (0, 0, C.generatorTransferRemainder i ξ η (C.Θ η ξ)) := by
  classical
  rw [C.transfer_kernel_chain_rule hΨ i hξ hη hne]
  simp_rw [← smul_eq_mul, ← map_smul]
  rw [← map_sum, ← map_add, ← map_add]
  congr 1
  simp only [Prod.smul_mk, smul_zero, ← prod_mk_sum, Finset.sum_const_zero,
    Prod.mk_add_mk, add_zero, zero_add]

end RothschildStein.P1.LiftedChart

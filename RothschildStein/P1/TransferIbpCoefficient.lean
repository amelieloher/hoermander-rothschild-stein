-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GeneratorTransferCoefficients
public import RothschildStein.P1.AdjointExpansion
public import RothschildStein.G1.BracketAlgebra
public import RothschildStein.G2.PolynomialCalculus
public import RothschildStein.P1.KernelEstimatesChart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Joint endpoint coefficient of a transfer
kernel. Its derivatives are taken before integration by parts
(BB (11.36)–(11.37), pp. 555–556). -/
def transferEndpointCoefficient (i : Fin k) (j : Fin (n+m))
    (p : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) : ℝ :=
  MvPolynomial.eval (C.Θ p.2 p.1) (C.generatorTransferCoefficient i j)

/-- The transfer coefficient is smooth jointly
on the actual chart patch; global smoothness of Θ is unnecessary. -/
theorem transferEndpointCoefficient_smooth (i : Fin k) (j : Fin (n+m)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.transferEndpointCoefficient i j) (C.U ×ˢ C.U) :=
  (G2.contDiff_eval _).comp_contDiffOn
    (C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩))

/-- The lower-order coefficient left by input
integration by parts includes both the coefficient derivative and the
full Euclidean divergence of the actual input bracket (BB p. 555). -/
def transferIbpCoefficient (i : Fin k) (j : Fin (n+m))
    (p : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) : ℝ :=
  fderiv ℝ (C.transferEndpointCoefficient i j) p (0, wordBracket C.Xl (C.B j) p.2) +
    Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) p.2 *
      C.transferEndpointCoefficient i j p

/-- The complete integration-by-parts
coefficient is smooth on the endpoint patch (BB Theorem 11.24). -/
theorem transferIbpCoefficient_smooth (i : Fin k) (j : Fin (n+m)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.transferIbpCoefficient i j) (C.U ×ˢ C.U) := by
  have hX : ∀ l, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl l) C.U :=
    fun l => (C.lift_smooth l).mono C.U_subset_O
  have hB := G1.wordBracket_contDiffOn C.isOpen_U C.Xl hX (C.B j)
  have hBp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) => wordBracket C.Xl (C.B j) p.2)
      (C.U ×ˢ C.U) := hB.comp contDiffOn_snd (fun _ hp => hp.2)
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (C.transferEndpointCoefficient i j))
      (C.U ×ˢ C.U) := (C.transferEndpointCoefficient_smooth i j).fderiv_of_isOpen
    (C.isOpen_U.prod C.isOpen_U) (by simp)
  have hdiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) =>
        Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) p.2)
      (C.U ×ˢ C.U) := (contDiffOn_euclideanDivergence ⟨C.U, C.isOpen_U⟩
    (wordBracket C.Xl (C.B j)) hB).comp contDiffOn_snd (fun _ hp => hp.2)
  exact (hd.clm_apply (contDiffOn_const.prodMk hBp)).add
    (hdiv.mul (C.transferEndpointCoefficient_smooth i j))

/-- The joint derivative is exactly the input
fiber derivative, with the output endpoint held fixed (BB p. 555). -/
theorem transferIbpCoefficient_eq (i : Fin k) (j : Fin (n+m))
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    C.transferIbpCoefficient i j (ξ, η) =
      fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => MvPolynomial.eval (C.Θ ζ ξ) (C.generatorTransferCoefficient i j)) η +
      Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) η *
        MvPolynomial.eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) := by
  have hd := ((C.transferEndpointCoefficient_smooth i j).contDiffAt
    ((C.isOpen_U.prod C.isOpen_U).mem_nhds (show (ξ, η) ∈ C.U ×ˢ C.U from ⟨hξ, hη⟩))).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp η ((hasFDerivAt_const ξ η).prodMk (hasFDerivAt_id η))
  change HasFDerivAt (fun ζ => C.transferEndpointCoefficient i j (ξ, ζ)) _ η at hc
  change fderiv ℝ (C.transferEndpointCoefficient i j) (ξ, η)
    (0, wordBracket C.Xl (C.B j) η) + _ =
    fderiv ℝ (fun ζ => C.transferEndpointCoefficient i j (ξ, ζ)) η
      (wordBracket C.Xl (C.B j) η) + _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, transferEndpointCoefficient]

end RothschildStein.P1.LiftedChart

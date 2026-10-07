-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformTransferCoordinateFluxBound
public import RothschildStein.P1.TransferRemainderFieldFlux
public import RothschildStein.P1.TransferFluxIntegrability
public import RothschildStein.P1.PrincipalModelDerivative
public import RothschildStein.H1.FieldSubtractConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The entire transfer remainder flux is
uniformly O(ε) on compact output sets, including the critical degree. -/
theorem exists_uniform_transfer_field_flux_bound
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) (i : Fin k)
    {β : ℝ} (hβ : ((w i : ℕ) : ℝ) - C.G.homogeneousDimension ≤ β)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ζ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      Ψ ζ η (C.G.dilate r u) = r ^ β * Ψ ζ η u)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ K,
      ‖(∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v) (θ ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u)‖ ≤ A * ε := by
  classical
  choose A hA hb using fun j =>
    C.exists_uniform_transfer_coordinate_flux_bound hK hKU i j hβ Ψ hΨ hhom hθ hsθ heθ ψ
  refine ⟨∑ j, A j, Finset.sum_nonneg (fun j _ => hA j), ?_⟩
  have hall := (Filter.eventually_all_finset Finset.univ).2 (fun j _ => hb j)
  filter_upwards [hall] with ε hε
  intro ξ hξ
  rw [C.integral_inputModel_transfer_fieldCutoff (hKU hξ) i Ψ hΨ hθ heθ]
  calc
    _ ≤ ∑ j, ‖∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u j *
      fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, A j * ε := Finset.sum_le_sum (fun j hj => hε j hj ξ hξ)
    _ = _ := (Finset.sum_mul _ _ _).symm

end RothschildStein.P1.LiftedChart

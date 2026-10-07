-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputRemainderFlux
public import RothschildStein.P1.InputModelCutoffIntegrability
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

/-- The full reflected remainder flux is the
finite sum of its integrable coordinate fluxes, including every coordinate. -/
theorem integral_inputModel_remainder_fieldCutoff
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) (θ ∘ C.G.dilate ε⁻¹) u *
      C.reflectedTransport ξ ψ u) =
    ∑ j, ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u * C.R [i] ξ (-u) j *
      fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u := by
  classical
  have he : (fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) (θ ∘ C.G.dilate ε⁻¹) u *
      C.reflectedTransport ξ ψ u) = fun u => ∑ j,
        Ψ ξ ((C.e ξ).symm (-u)) u * C.R [i] ξ (-u) j *
          fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u := by
    funext u
    rw [fieldDerivative_coordinate_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun j _ =>
    C.integrable_inputModel_remainder_coordinateCutoff hξ i j Ψ hΨ hθ heθ ε ψ)]

/-- Every full remainder cutoff row is integrable before taking its limit. -/
theorem integrable_inputModel_remainder_fieldCutoff
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Integrable (fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) (θ ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun j _ =>
    C.integrable_inputModel_remainder_coordinateCutoff hξ i j Ψ hΨ hθ heθ ε ψ)
  apply hi.congr
  apply Eventually.of_forall
  intro u
  change (∑ j, Ψ ξ ((C.e ξ).symm (-u)) u * C.R [i] ξ (-u) j *
    fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u) =
    Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) (θ ∘ C.G.dilate ε⁻¹) u *
      C.reflectedTransport ξ ψ u
  rw [fieldDerivative_coordinate_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual full reflected remainder has
zero flux at every admissible principal degree. -/
theorem tendsto_input_remainder_field_flux
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    {β : ℝ} (hβ : ((w i : ℕ) : ℝ) - C.G.homogeneousDimension ≤ β)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ζ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      Ψ ζ η (C.G.dilate r u) = r ^ β * Ψ ζ η u)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) (θ ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := tendsto_finsetSum Finset.univ (fun j _ =>
    C.tendsto_input_remainder_coordinate_flux hξ i j hβ Ψ hΨ hhom hθ hsθ heθ ψ)
  simpa only [C.integral_inputModel_remainder_fieldCutoff hξ i Ψ hΨ hθ heθ,
    Finset.sum_const_zero] using ht

/-- The exterior cutoff preserves the zero full remainder flux. -/
theorem tendsto_input_remainder_exterior_field_flux
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    {β : ℝ} (hβ : ((w i : ℕ) : ℝ) - C.G.homogeneousDimension ≤ β)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ζ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      Ψ ζ η (C.G.dilate r u) = r ^ β * Ψ ζ η u)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have he (ε : ℝ) : (∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) = -(∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) (θ ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) := by
    have hder : fieldDerivative (fun v => C.R [i] ξ (-v))
        ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) =
        fun u => -fieldDerivative (fun v => C.R [i] ξ (-v)) (θ ∘ C.G.dilate ε⁻¹) u :=
      H1.fieldDerivative_one_sub_C1 _
        ((hθ.comp (G2.contDiff_dilate C.G ε⁻¹)).of_le (by simp))
    rw [hder, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall (fun u => by ring))
  simp_rw [he]
  simpa only [neg_zero] using
    (C.tendsto_input_remainder_field_flux hξ i hβ Ψ hΨ hhom hθ hsθ heθ ψ).neg

end RothschildStein.P1.LiftedChart

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.VariableCoordinateCutoffScaling
public import RothschildStein.P1.RescaledRemainderIntegralLimit
public import RothschildStein.P1.ReflectedChartTransport
public import RothschildStein.H1.FieldCutoffSupport

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

/-- Every principal potential degree at or
above the critical degree has zero full remainder coordinate flux.
This reuses the weighted O(ε) estimate and the exact coordinate scaling. -/
theorem tendsto_input_remainder_coordinate_flux
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k) (j : Fin (n + m))
    {β : ℝ} (hβ : ((w i : ℕ) : ℝ) - C.G.homogeneousDimension ≤ β)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ζ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      Ψ ζ η (C.G.dilate r u) = r ^ β * Ψ ζ η u)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u * C.R [i] ξ (-u) j *
      fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let E := fun _ : Fin (n + m) → ℝ => (Pi.single j 1 : Fin (n + m) → ℝ)
  let D := fieldDerivative E θ
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := H1.smooth_fieldDerivative E contDiff_const θ hθ
  have hsD : HasCompactSupport D := hsθ.of_isClosed_subset isClosed_closure
    (S.tsupport_fieldDerivative_subset E θ)
  have h0D : (0 : Fin (n + m) → ℝ) ∉ tsupport D :=
    notMem_tsupport_iff_eventuallyEq.mpr (H1.fieldDerivative_cutoff_eventually_zero E heθ)
  obtain ⟨hcψ, hsψ⟩ := C.reflectedTransport_regular hξ ψ
  have ht := C.tendsto_rescaledInput_remainder_integral hξ i j Ψ hΨ D
    hD.continuous hsD h0D (C.reflectedTransport ξ ψ) hcψ.continuous hsψ
  have htε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hgain : 0 ≤ β + (C.G.homogeneousDimension : ℝ) - ((w i : ℕ) : ℝ) := by linarith
  have hlim := (htε.rpow_const (Or.inr hgain)).mul ht
  simp only [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he := integral_variableCoordinateCutoff_dilate C.G j ((w i : ℕ) : ℝ) β Ψ hhom
    (fun u => (ξ, (C.e ξ).symm (-u))) (fun u => C.R [i] ξ (-u) j)
    (C.reflectedTransport ξ ψ) hθ hε
  exact he.symm

end RothschildStein.P1.LiftedChart

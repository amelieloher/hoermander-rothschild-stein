-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.VariableCoordinateCutoffScaling
public import RothschildStein.P1.UniformTransferIntegralBound
public import RothschildStein.P1.UniformReflectedTransportBound
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
above the critical degree has uniformly O(ε) full remainder coordinate flux.
This reuses the weighted O(ε) estimate and the exact coordinate scaling. -/
theorem exists_uniform_transfer_coordinate_flux_bound
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) (i : Fin k) (j : Fin (n + m))
    {β : ℝ} (hβ : ((w i : ℕ) : ℝ) - C.G.homogeneousDimension ≤ β)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ζ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      Ψ ζ η (C.G.dilate r u) = r ^ β * Ψ ζ η u)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ K,
      ‖(∫ u, Ψ ξ ((C.e ξ).symm (-u)) u * C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u j *
      fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u)‖ ≤ A * ε := by
  let E := fun _ : Fin (n + m) → ℝ => (Pi.single j 1 : Fin (n + m) → ℝ)
  let D := fieldDerivative E θ
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := H1.smooth_fieldDerivative E contDiff_const θ hθ
  have hsD : HasCompactSupport D := hsθ.of_isClosed_subset isClosed_closure
    (S.tsupport_fieldDerivative_subset E θ)
  have h0D : (0 : Fin (n + m) → ℝ) ∉ tsupport D :=
    notMem_tsupport_iff_eventuallyEq.mpr (H1.fieldDerivative_cutoff_eventually_zero E heθ)
  obtain ⟨B, hB, hBφ⟩ := C.exists_uniform_reflectedTransport_bound hK hKU ψ
  obtain ⟨A, hA, hbound⟩ := C.exists_uniform_rescaledTransfer_integral_bound hK hKU i j Ψ hΨ D
    hD.continuous hsD h0D (C.reflectedTransport · ψ) B hB hBφ
  have hgain : 0 ≤ β + (C.G.homogeneousDimension : ℝ) - ((w i : ℕ) : ℝ) := by linarith
  refine ⟨A, hA, ?_⟩
  filter_upwards [hbound, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with ε hb hε hε1
  intro ξ hξ
  have he := integral_variableCoordinateCutoff_dilate C.G j ((w i : ℕ) : ℝ) β Ψ hhom
    (fun u => (ξ, (C.e ξ).symm (-u)))
    (fun u => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u j)
    (C.reflectedTransport ξ ψ) hθ hε
  rw [he, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hε _)]
  have hp : ε ^ (β + (C.G.homogeneousDimension : ℝ) - ((w i : ℕ) : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le hgain
  calc
    _ ≤ ε ^ (β + (C.G.homogeneousDimension : ℝ) - ((w i : ℕ) : ℝ)) * (A * ε) :=
      mul_le_mul_of_nonneg_left (hb ξ hξ) (Real.rpow_nonneg hε.le _)
    _ ≤ 1 * (A * ε) := mul_le_mul_of_nonneg_right hp (mul_nonneg hA hε.le)
    _ = _ := one_mul _

end RothschildStein.P1.LiftedChart

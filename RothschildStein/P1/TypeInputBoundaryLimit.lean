-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputBoundaryMultiplier
public import RothschildStein.P1.RegularInputBoundaryFlux
public import RothschildStein.P1.InputBoundaryIntegrability
public import RothschildStein.P1.PrincipalLeadingTypes
public import RothschildStein.P1.FiniteRowAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Evaluation of the actual finite smooth multiplier preserves every
principal term and its multiplicity. -/
theorem typeInputBoundaryMultiplier_apply
    {lam : ℕ} {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hF : C.IsStandardFrame F H K hQ) (d : TypeDecomposition F lam 1 κ) (i : Fin k)
    (ξ : Fin (n + m) → ℝ) :
    C.typeInputBoundaryMultiplier hF d i ξ =
      (d.principal.map (fun t => C.principalInputBoundaryMultiplier hF t i ξ)).sum := by
  have he (l : List (TestFunction F.V ℝ (⊤ : ℕ∞))) :
      l.sum ξ = (l.map (fun μ => μ ξ)).sum := by
    induction l with
    | nil => simp only [List.sum_nil, List.map_nil, FunLike.coe_zero, Pi.zero_apply]
    | cons μ l ih =>
      simp only [List.sum_cons, List.map_cons, FunLike.coe_add, Pi.add_apply, ih]
  simpa only [typeInputBoundaryMultiplier, List.map_map, Function.comp_def] using
    he (d.principal.map (fun t => C.principalInputBoundaryMultiplier hF t i))

/-- The complete actual type-kernel boundary
flux tends to the constructed smooth multiplier. Finite integrability
is proved before decomposition and before integral linearity. -/
theorem tendsto_typeInput_boundary_multiplier
    {lam : ℕ} {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hF : C.IsStandardFrame F H K hQ) (hκ : IsTypeKernel F lam κ)
    (d : TypeDecomposition F lam 1 κ) (i : Fin k) (hw : (w i : ℕ) ≤ lam)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η, -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ ζ ξ)))) η) *
        κ ξ η * φ η) (𝓝[>] (0 : ℝ))
      (𝓝 (C.typeInputBoundaryMultiplier hF d i ξ * φ ξ)) := by
  let rsTypeInputBoundaryFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  let B := fun (ε : ℝ) (r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (η : Fin (n + m) → ℝ) => -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ ζ ξ)))) η) * r ξ η * φ η
  have hd (t : PrincipalTerm F) (ht : t ∈ d.principal) : t.degree ≤ 2 - ((w i : ℕ) : ℤ) := by
    have hh := d.principal_degree t ht
    omega
  have hiP (ε : ℝ) (t : PrincipalTerm F) (ht : t ∈ d.principal) : Integrable (B ε t.kernel) :=
    C.isTypeKernel_integrable_inputBoundary hF.lifted (t.isTypeKernel 0 (by
      have hh := hd t ht
      simp only [Nat.cast_zero, sub_zero]
      omega)) hξ i (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
      (radialGaugeCutoff_eventually_one H.norm.gauge) ε φ
  have hiK (ε : ℝ) : Integrable (B ε κ) :=
    C.isTypeKernel_integrable_inputBoundary hF.lifted hκ hξ i
      (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
      (radialGaugeCutoff_eventually_one H.norm.gauge) ε φ
  have hiS (ε : ℝ) : Integrable (fun η => (d.principal.map (fun t => B ε t.kernel η)).sum) :=
    integrable_listMapSum d.principal (fun t => B ε t.kernel) (hiP ε)
  have heP (ε : ℝ) (η : Fin (n + m) → ℝ) :
      (d.principal.map (fun t => B ε t.kernel η)).sum =
        -(fieldDerivative (C.Xl i)
          (fun ζ => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ ζ ξ)))) η) *
          (d.principal.map (fun t => t.kernel ξ η)).sum * φ η := by
    simp only [B, List.sum_map_mul_right, List.sum_map_mul_left]
  have he (ε : ℝ) : B ε κ =ᵐ[volume] fun η =>
      (d.principal.map (fun t => B ε t.kernel η)).sum + B ε d.regular η := by
    filter_upwards [volume.ae_ne ξ] with η hη
    rw [heP]
    dsimp only [B]
    rw [d.eq_off_diagonal ξ η hη.symm]
    ring
  have hiR (ε : ℝ) : Integrable (B ε d.regular) := by
    apply ((hiK ε).sub (hiS ε)).congr
    filter_upwards [he ε] with η hη
    change B ε κ η - (d.principal.map (fun t => B ε t.kernel η)).sum = B ε d.regular η
    rw [hη]
    ring
  have heI (ε : ℝ) : (∫ η, B ε κ η) =
      (d.principal.map (fun t => ∫ η, B ε t.kernel η)).sum + ∫ η, B ε d.regular η := by
    rw [integral_congr_ae (he ε), integral_add (f := fun η =>
      (d.principal.map (fun t => B ε t.kernel η)).sum) (g := B ε d.regular) (hiS ε) (hiR ε),
      integral_listMapSum d.principal (fun t => B ε t.kernel) (hiP ε)]
  have htP := tendsto_list_sum d.principal (fun t ht =>
    C.tendsto_principalInput_boundary_multiplier hF t i (hd t ht) hξ φ)
  have htR := C.tendsto_regularInput_boundary_flux hF d.regular_isRegular i hξ φ
  have ht := htP.add htR
  simp only [add_zero] at ht
  rw [C.typeInputBoundaryMultiplier_apply hF d i ξ, ← List.sum_map_mul_right]
  change Tendsto (fun ε => ∫ η, B ε κ η) _ _
  simpa only [heI] using ht

end RothschildStein.P1.LiftedChart

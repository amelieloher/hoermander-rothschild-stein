-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CriticalPrincipalBoundaryFlux
public import RothschildStein.P1.SubcriticalPrincipalBoundaryFlux
public import RothschildStein.P1.StandardFrame
public import RothschildStein.P1.RadialGaugeCutoff

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

/-- Only a critical principal degree contributes
an input boundary multiplier; subcritical degrees contribute zero. -/
def principalInputBoundaryMultiplier (hF : C.IsStandardFrame F H K hQ)
    (t : PrincipalTerm F) (i : Fin k) : TestFunction F.V ℝ (⊤ : ℕ∞) :=
  if t.degree = 2 - ((w i : ℕ) : ℤ) then
    C.endpointFluxMultiplier F (subset_closure.trans hF.lifted.closure_subset) t
      (hF.lifted.pole_smooth t.star) (fun v => C.Y i (-v)) (C.reflectedGenerator_contDiff i)
      (fun u => radialCutoffProfile (H.norm u))
      (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
      (radialGaugeCutoff_hasCompactSupport H.norm.gauge)
      (radialGaugeCutoff_eventually_one H.norm.gauge)
  else 0

/-- The actual principal boundary row tends to its constructed smooth
multiplier, at every degree allowed by input differentiation. -/
theorem tendsto_principalInput_boundary_multiplier (hF : C.IsStandardFrame F H K hQ)
    (t : PrincipalTerm F) (i : Fin k) (hd : t.degree ≤ 2 - ((w i : ℕ) : ℤ))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η, -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ ζ ξ)))) η) *
        t.kernel ξ η * φ η) (𝓝[>] (0 : ℝ))
      (𝓝 (C.principalInputBoundaryMultiplier hF t i ξ * φ ξ)) := by
  by_cases he : t.degree = 2 - ((w i : ℕ) : ℤ)
  · simp only [principalInputBoundaryMultiplier, ite_eq_left he]
    exact C.tendsto_criticalPrincipal_input_boundary_flux hF.lifted t i he
      (hF.lifted.closure_subset (subset_closure hξ))
      (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
      (radialGaugeCutoff_hasCompactSupport H.norm.gauge)
      (radialGaugeCutoff_eventually_one H.norm.gauge) φ
  · simp only [principalInputBoundaryMultiplier, ite_eq_right he, FunLike.coe_zero, Pi.zero_apply, zero_mul]
    exact C.tendsto_subcriticalPrincipal_input_boundary_flux hF.lifted t i (lt_of_le_of_ne hd he)
      (hF.lifted.closure_subset (subset_closure hξ))
      (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
      (radialGaugeCutoff_hasCompactSupport H.norm.gauge)
      (radialGaugeCutoff_eventually_one H.norm.gauge) φ

/-- A principal term of strictly higher input type has no multiplier. -/
theorem principalInputBoundaryMultiplier_eq_zero_of_type_gt
    (hF : C.IsStandardFrame F H K hQ) (t : PrincipalTerm F) (i : Fin k)
    {lam : ℕ} (hw : (w i : ℕ) < lam) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    C.principalInputBoundaryMultiplier hF t i = 0 := by
  have he : t.degree ≠ 2 - ((w i : ℕ) : ℤ) := by omega
  simp only [principalInputBoundaryMultiplier, ite_eq_right he]

/-- The full decomposition multiplier is an
actual finite sum of compact smooth critical endpoint multipliers. -/
def typeInputBoundaryMultiplier {lam : ℕ} {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hF : C.IsStandardFrame F H K hQ) (d : TypeDecomposition F lam 1 κ) (i : Fin k) :
    TestFunction F.V ℝ (⊤ : ℕ∞) :=
  (d.principal.map (fun t => C.principalInputBoundaryMultiplier hF t i)).sum

/-- The constructed full multiplier vanishes for a positive output type. -/
theorem typeInputBoundaryMultiplier_eq_zero_of_type_gt
    {lam : ℕ} {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hF : C.IsStandardFrame F H K hQ) (d : TypeDecomposition F lam 1 κ) (i : Fin k)
    (hw : (w i : ℕ) < lam) : C.typeInputBoundaryMultiplier hF d i = 0 := by
  unfold typeInputBoundaryMultiplier
  apply List.sum_eq_zero
  intro μ hμ
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hμ
  exact C.principalInputBoundaryMultiplier_eq_zero_of_type_gt hF t i hw (d.principal_degree t ht)

end RothschildStein.P1.LiftedChart

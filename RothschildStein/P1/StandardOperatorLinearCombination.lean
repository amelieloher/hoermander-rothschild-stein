-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeOperatorRadialLimit
public import RothschildStein.P1.InputBoundaryIntegrability

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

/-- Algebra of actual standard-frame actions on
tests, including type zero and different input types. Finite radial
integrability is proved before the linear combination is integrated. -/
theorem typeOperator_apply_of_kernel_linear_combination {a b c : ℕ}
    (hF : C.IsStandardFrame F H K hQ)
    (S : TypeOperator F a) (T : TypeOperator F b) (U : TypeOperator F c)
    (α β : (Fin (n + m) → ℝ) → ℝ)
    (hk : ∀ ξ η, S.kernel ξ η = α ξ * T.kernel ξ η + β ξ * U.kernel ξ η)
    (hμ : ∀ ξ, S.mult ξ = α ξ * T.mult ξ + β ξ * U.mult ξ)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) :
    S.apply φ ξ = α ξ * T.apply φ ξ + β ξ * U.apply φ ξ := by
  let χ := fun ε η => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))
  have hi {d : ℕ} (V : TypeOperator F d) (ε : ℝ) :
      Integrable (fun η => χ ε η * (V.kernel ξ η * φ η)) := by
    have h := C.isTypeKernel_integrable_inputCutoff hF.lifted V.isType hξ
      (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
      (radialGaugeCutoff_eventually_one H.norm.gauge) ε φ
    exact h.congr (Eventually.of_forall (fun η => by dsimp only [χ]; ring))
  have he (ε : ℝ) : (∫ η, χ ε η * (S.kernel ξ η * φ η)) =
      α ξ * (∫ η, χ ε η * (T.kernel ξ η * φ η)) +
      β ξ * (∫ η, χ ε η * (U.kernel ξ η * φ η)) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi T ε).const_mul _) ((hi U ε).const_mul _)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun η => by dsimp only; rw [hk]; ring)
  have ht := ((C.typeOperator_tendsto_radialIntegral hF T φ hξ).const_mul (α ξ)).add
    ((C.typeOperator_tendsto_radialIntegral hF U φ hξ).const_mul (β ξ))
  have heLimit := tendsto_nhds_unique (C.typeOperator_tendsto_radialIntegral hF S φ hξ)
    (ht.congr' (Eventually.of_forall (fun ε => (he ε).symm)))
  rw [hμ] at heLimit
  nlinarith

end RothschildStein.P1.LiftedChart

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalFourTermConstructed
public import RothschildStein.P1.ChartRemainderDerivativeType
public import RothschildStein.P1.ModelHypotheses

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual principal kernel derivative
has the four required pointwise contributions of types λ-w_i, λ+1-w_i,
λ and λ. In particular the horizontal and drift budgets are both covered.
This is the constructed pointwise type statement; no principal-value or
weak operator identity is asserted here (BB Lemma 11.18, p. 549). -/
theorem LiftedChart.exists_principal_fourTerm_types
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G)
    (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (i : Fin k) (lam : ℕ)
    (hw : (w i : ℕ) ≤ lam) (hd : t.degree ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    ∃ kLead kRem kCut kParam : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ,
      IsTypeKernel F (lam - (w i : ℕ)) kLead ∧
      IsTypeKernel F (lam + 1 - (w i : ℕ)) kRem ∧
      IsTypeKernel F lam kCut ∧ IsTypeKernel F lam kParam ∧
      ∀ ξ ∈ C.U, ∀ η ∈ C.U, ξ ≠ η →
        fieldDerivative (C.Xl i) (fun ζ => t.kernel ζ η) ξ =
          kCut ξ η + kParam ξ η + kLead ξ η + kRem ξ η := by
  have hhY : G2.IsHomogeneousField F.G (C.Y i) ((w i : ℕ) : ℤ) := by
    simpa only [hG, Int.cast_natCast] using C.isHomogeneousField i
  have hX : ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    (C.lift_smooth i).mono (hVU.trans C.U_subset_O)
  refine ⟨t.leadingKernel (C.Y i) (C.model_field_smooth i) ((w i : ℕ) : ℤ) hhY,
    (fun ξ η => t.a ξ * t.b η * fieldDerivative (C.R [i] η) (t.modelKernel ξ η) (F.Θ η ξ)),
    (t.cutoffDerivative (C.Xl i) hX).kernel, t.endpointKernel (C.Xl i) hX,
    t.leadingKernel_isTypeKernel (C.Y i) (C.model_field_smooth i) (w i : ℕ) lam hhY hw hd,
    C.isTypeKernel_chart_remainder_derivative F hΘ hG hVU t i lam hw hd hΓ hhom,
    t.cutoffDerivative_isTypeKernel (C.Xl i) hX lam hd,
    t.endpointKernel_isTypeKernel (C.Xl i) hX lam hd, ?_⟩
  intro ξ hξ η hη hne
  exact C.principal_fourTermConstructed F hΘ hVU t i hhY hΓ hξ hη hne

end RothschildStein.P1

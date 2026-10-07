-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LocalExtensionRegularKernel
public import RothschildStein.P1.PrincipalLeadingTerms
public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.P1.TypeClosure

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Replacing a local coefficient by a smooth
extension agreeing near the pole changes its product with a whole
principal model kernel by an actual compact C^m remainder. -/
theorem LiftedChart.isRegularKernel_local_principal_extension_difference
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (budget : ℕ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (A B : (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)) → ℝ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => A (p, F.Θ p.2 p.1)) (C.U ×ˢ C.U))
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (ε : ℝ) (hε : 0 < ε)
    (he : ∀ p ∈ tsupport t.a ×ˢ tsupport t.b, ∀ u : Fin (n + m) → ℝ,
      ‖u‖ ≤ ε → B (p, u) = A (p, u)) :
    IsRegularKernel F budget (fun ξ η => t.a ξ * t.b η *
      ((A ((ξ, η), F.Θ η ξ) - B ((ξ, η), F.Θ η ξ)) * t.modelKernel ξ η (F.Θ η ξ))) := by
  classical
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => F.Θ p.2 p.1) (C.U ×ˢ C.U) := by
    rw [hΘ]
    exact C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)
  have hterm (α : Fin (n + m) → ℕ) (hα : α ∈ t.indices) :
      IsRegularKernel F budget (fun ξ η => t.a ξ * t.b η *
        ((A ((ξ, η), F.Θ η ξ) - B ((ξ, η), F.Θ η ξ)) *
          ((t.D ξ η).coefficient α (F.Θ η ξ) * euclideanPartial α (F.pole t.star) (F.Θ η ξ)))) := by
    have hc := t.coefficientLeft_contDiff α hα
    have hAc := hA.mul (hc.comp_contDiffOn (contDiffOn_id.prodMk hθ))
    have hBc := hB.mul hc
    have hg : ContDiffOn ℝ (⊤ : ℕ∞)
        (euclideanPartial α (F.pole t.star)) {(0 : Fin (n + m) → ℝ)}ᶜ := by
      apply contDiffOn_iff_forall_nat_le.mpr
      intro j _
      exact H1.contDiffOn_euclideanPartial_finite
        ⟨{(0 : Fin (n + m) → ℝ)}ᶜ, isOpen_compl_singleton⟩ α j (F.pole t.star)
        (hΓ.of_le (by simp))
    have h := C.isRegularKernel_local_extension_difference F hΘ hVU budget t.a t.b
      (fun q => A q * t.coefficientLeft α q) (fun q => B q * t.coefficientLeft α q)
      hAc hBc (euclideanPartial α (F.pole t.star)) hg ε hε
      (fun p hp u hu => by rw [he p hp u hu])
    convert h using 1
    funext ξ η
    dsimp only [PrincipalTerm.coefficientLeft]
    ring
  have hsum := IsRegularKernel.sum t.indices hterm
  convert hsum using 1
  funext ξ η
  simp only [PrincipalTerm.modelKernel, SmoothDifferentialOperator.apply, t.indices_eq, Finset.mul_sum]

end RothschildStein.P1

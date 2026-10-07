-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedPrincipalCoefficientType
public import RothschildStein.P1.LocalPrincipalExtensionRegular

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- A coefficient smooth on the actual open
chart domain, with lower weighted jets vanishing only on the cutoff patch,
times a whole principal operator has the sharp type degree(D)-low.
The extension, finite principal expansion and regular difference are constructed. -/
theorem LiftedChart.isTypeKernel_local_weighted_principal
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (low lam : ℕ)
    (hdegree : t.degree - (low : ℤ) ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u)
    (T : Set ((((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ))))
    (hT : IsOpen T)
    (A : (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)) → ℝ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A T)
    (hTzero : ∀ p ∈ tsupport t.a ×ˢ tsupport t.b, (p, (0 : Fin (n + m) → ℝ)) ∈ T)
    (hTθ : ∀ p ∈ C.U ×ˢ C.U, (p, F.Θ p.2 p.1) ∈ T)
    (hjet : ∀ p ∈ tsupport t.a ×ˢ tsupport t.b, ∀ I : List (Fin (n + m)),
      (I.map F.G.weight).sum < low → rsPartial I (fun u => A (p, u)) 0 = 0) :
    IsTypeKernel F lam (fun ξ η => t.a ξ * t.b η *
      (A ((ξ, η), F.Θ η ξ) * t.modelKernel ξ η (F.Θ η ξ))) := by
  obtain ⟨B, hB, ε, hε, he⟩ := exists_global_extension_generic_parameter T hT A hA
    (tsupport t.a ×ˢ tsupport t.b) (t.a.hasCompactSupport.prod t.b.hasCompactSupport) hTzero
  have hjetB := extension_preserves_weighted_jets F.G A B
    (tsupport t.a ×ˢ tsupport t.b) ε hε he low hjet
  have hmain := C.isTypeKernel_patch_weighted_principal F hΘ hVU t low lam
    hdegree hΓ hhom B hB hjetB
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => F.Θ p.2 p.1) (C.U ×ˢ C.U) := by
    rw [hΘ]
    exact C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)
  have hAθ := hA.comp (contDiffOn_id.prodMk hθ) hTθ
  let r := fun ξ η => t.a ξ * t.b η *
    ((A ((ξ, η), F.Θ η ξ) - B ((ξ, η), F.Θ η ξ)) * t.modelKernel ξ η (F.Θ η ξ))
  have hregular : ∀ budget, IsRegularKernel F budget r := fun budget =>
    C.isRegularKernel_local_principal_extension_difference F hΘ hVU t budget hΓ A B hAθ hB ε hε he
  have hr := isTypeKernel_of_all_regular lam r hregular
  have hs := hmain.add hr
  have hsum : (fun ξ η => t.a ξ * t.b η *
      (B ((ξ, η), F.Θ η ξ) * t.modelKernel ξ η (F.Θ η ξ)) + r ξ η) =
      (fun ξ η => t.a ξ * t.b η *
        (A ((ξ, η), F.Θ η ξ) * t.modelKernel ξ η (F.Θ η ξ))) := by
    funext ξ η
    dsimp only [r]
    ring
  rw [hsum] at hs
  exact hs

end RothschildStein.P1

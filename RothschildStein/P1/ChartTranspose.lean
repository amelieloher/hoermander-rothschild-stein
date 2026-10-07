-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeTranspose
public import RothschildStein.P1.KernelEstimatesChart

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace RothschildStein.P1

/-- H1's single adjoint-pole reflection identity supplies both
Boolean pole choices, without assigning a special value at zero. -/
theorem KernelFrame.pole_not_eq_reflection {N : ℕ} (F : KernelFrame N)
    (hΓs : ∀ u : Fin N → ℝ, u ≠ 0 → F.Γs u = F.Γ (-u)) :
    ∀ b : Bool, ∀ u : Fin N → ℝ, u ≠ 0 → F.pole (!b) u = F.pole b (-u) := by
  intro b u hu
  cases b with
  | false => exact hΓs u hu
  | true =>
    change F.Γ u = F.Γs (-u)
    rw [hΓs (-u) (neg_ne_zero.mpr hu), neg_neg]

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual lifted chart and H1 adjoint poles give the full
same-type transposed kernel, for every finite regularity budget. -/
theorem LiftedChart.isTypeKernel_transpose
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓs : ∀ u : Fin (n + m) → ℝ, u ≠ 0 → F.Γs u = F.Γ (-u))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) F.Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hΓstar : ContDiffOn ℝ (⊤ : ℕ∞) F.Γs {(0 : Fin (n + m) → ℝ)}ᶜ)
    (lam : ℕ) (κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hκ : IsTypeKernel F lam κ) : IsTypeKernel F lam (fun ξ η => κ η ξ) := by
  apply hκ.transpose (F.pole_not_eq_reflection hΓs)
  · intro b
    cases b with
    | false => exact hΓ
    | true => exact hΓstar
  · intro ξ hξ η hη
    rw [hΘ]
    exact C.theta_antisymm ξ (hVU hξ) η (hVU hη)
  · intro ξ hξ η hη hne
    rw [hΘ]
    exact (C.theta_eq_zero_iff (hVU hξ) (hVU hη)).not.mpr hne.symm

end RothschildStein.P1

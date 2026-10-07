-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ErrorTypesClosure
public import RothschildStein.P1.ChartTranspose

/-!
# Parametrix error types: the transpose swaps the pole of a modeled kernel

The transposed principal term of `PrincipalTerm.transpose` swaps the cutoffs, reflects the differential
operator and swaps the pole (`Γ ↔ Γ*`, transposition of types, BB (11.12), p. 546; `Γ*(u) = Γ(-u)` and the antisymmetry
`Θ(ξ, η) = -Θ(η, ξ)`). Hence the transpose of a type-`lam` kernel modeled on the pole `star` is a
type-`lam` kernel modeled on `!star`:

* `IsTypeKernelOn.transpose` for an arbitrary frame carrying the transposition hypotheses;
* `LiftedChart.isTypeKernelOn_transpose` for the frames of a lifted chart whose poles are exchanged by
  inversion, the pole-tracked version of `LiftedChart.isTypeKernel_transpose`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- The transpose of a type-`lam` kernel modeled on `star` is a type-`lam` kernel modeled on
`!star`: the transposed decomposition has the transposed principal terms, whose poles are swapped. -/
theorem IsTypeKernelOn.transpose {N lam : ℕ} {F : KernelFrame N} {star : Bool}
    {κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hκ : IsTypeKernelOn F star lam κ)
    (hpole : ∀ b : Bool, ∀ u : Fin N → ℝ, u ≠ 0 → F.pole (!b) u = F.pole b (-u))
    (hsmooth : ∀ b : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole b) {(0 : Fin N → ℝ)}ᶜ)
    (hanti : ∀ ξ ∈ F.V, ∀ η ∈ F.V, F.Θ η ξ = -F.Θ ξ η)
    (hne : ∀ ξ ∈ F.V, ∀ η ∈ F.V, ξ ≠ η → F.Θ ξ η ≠ 0) :
    IsTypeKernelOn F (!star) lam (fun ξ η => κ η ξ) := by
  intro m
  obtain ⟨D, hD⟩ := hκ m
  refine ⟨D.transpose hpole hsmooth hanti hne, ?_⟩
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  change (!q.star) = !star
  rw [hD q hq]

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual lifted chart and H1 adjoint poles give the same-type transposed kernel modeled on
the swapped pole, for every finite regularity budget. -/
theorem LiftedChart.isTypeKernelOn_transpose
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓs : ∀ u : Fin (n + m) → ℝ, u ≠ 0 → F.Γs u = F.Γ (-u))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) F.Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hΓstar : ContDiffOn ℝ (⊤ : ℕ∞) F.Γs {(0 : Fin (n + m) → ℝ)}ᶜ)
    (star : Bool) (lam : ℕ) (κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hκ : IsTypeKernelOn F star lam κ) :
    IsTypeKernelOn F (!star) lam (fun ξ η => κ η ξ) := by
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

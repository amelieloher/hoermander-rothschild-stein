-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PositiveTypeMass
public import RothschildStein.P1.TypeKernelRepresentative
public import RothschildStein.P1.SchurRepresentativeTranspose

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual positive-type operator has the bilinear transpose
pairing of BB Proposition 11.14, pp. 545–546. Fubini is discharged from
its proved Schur masses; arbitrary diagonal values are allowed. The L1
input and bounded output test include both compactly supported smooth tests. -/
theorem LiftedChart.positiveType_bilinearTranspose
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓ : ∀ star : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ star : Bool, ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (lam : ℕ) (hlam : 1 ≤ lam)
    (κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) (hκ : IsTypeKernel F lam κ)
    (f g : (Fin (n + m) → ℝ) → ℝ)
    (hf : Measurable f) (hfi : Integrable f volume)
    (hg : Measurable g) (hgt : MemLp g ⊤ volume) :
    (∫ ξ, g ξ * (∫ η, κ ξ η * f η)) = ∫ η, f η * (∫ ξ, κ ξ η * g ξ) := by
  obtain ⟨A, B, hA, hB, ha, hb⟩ :=
    C.exists_positiveType_schur_bounds F hG hΘ hVU hΓ hhom lam hlam κ hκ
  obtain ⟨r, hr, he⟩ := C.exists_typeKernel_measurableRepresentative F hΘ hVU hΓ hκ
  have har : ∀ ξ, (∫⁻ η, ‖r ξ η‖ₑ) ≤ A := by
    intro ξ
    exact (lintegral_congr_ae ((he ξ).1.fun_comp (fun x : ℝ => ‖x‖ₑ))).le.trans (ha ξ)
  have hbr : ∀ η, (∫⁻ ξ, ‖r ξ η‖ₑ) ≤ B := by
    intro η
    exact (lintegral_congr_ae ((he η).2.fun_comp (fun x : ℝ => ‖x‖ₑ))).le.trans (hb η)
  exact schur_bilinearTranspose_of_representative volume volume κ r hr
    (fun ξ => (he ξ).1) (fun η => (he η).2) A B hA hB har hbr f hf hfi g hg hgt

end RothschildStein.P1

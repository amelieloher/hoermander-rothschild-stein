-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalRowMass
public import RothschildStein.P1.PrincipalColumnMass
public import RothschildStein.P1.PositiveTypeRowIntegrability
public import RothschildStein.P1.RegularKernelMass
public import RothschildStein.P1.KernelMassAdd

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Actual positive-type kernels have finite uniform absolute
row and column masses. Constants are chosen from one finite decomposition;
arbitrary diagonal values do not enter either integral. -/
theorem LiftedChart.exists_positiveType_schur_bounds
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓ : ∀ star : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ star : Bool, ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (lam : ℕ) (hlam : 1 ≤ lam)
    (kern : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) (hk : IsTypeKernel F lam kern) :
    ∃ A B : ℝ≥0∞, A ≠ ⊤ ∧ B ≠ ⊤ ∧
      (∀ ξ, (∫⁻ η, ‖kern ξ η‖ₑ) ≤ A) ∧ (∀ η, (∫⁻ ξ, ‖kern ξ η‖ₑ) ≤ B) := by
  let rsPositiveMassFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  obtain ⟨D⟩ := hk 0
  have hd : ∀ t ∈ D.principal, t.degree ≤ 1 := by
    intro t ht
    have he := D.principal_degree t ht
    omega
  obtain ⟨A, hA, ha⟩ := exists_list_sum_row_mass_bound D.principal
    (fun t => t.kernel)
    (fun t ht ξ => (C.integrable_principal_row F hG hΘ hVU t (hd t ht)
      (hΓ t.star) (hhom t.star) ξ).aestronglyMeasurable)
    (fun t ht => C.exists_principal_row_mass_bound F hG hΘ hVU t (hd t ht)
      (hΓ t.star) (hhom t.star))
  obtain ⟨B, hB, hb⟩ := exists_list_sum_row_mass_bound D.principal
    (fun t η ξ => t.kernel ξ η)
    (fun t ht η => (C.integrable_principal_column F hG hΘ hVU t (hd t ht)
      (hΓ t.star) (hhom t.star) η).aestronglyMeasurable)
    (fun t ht => C.exists_principal_column_mass_bound F hG hΘ hVU t (hd t ht)
      (hΓ t.star) (hhom t.star))
  obtain ⟨Ar, Br, hAr, hBr, har, hbr⟩ := D.regular_isRegular.exists_schur_bounds
  refine ⟨Ar + A, Br + B, ENNReal.add_ne_top.mpr ⟨hAr, hA⟩,
    ENNReal.add_ne_top.mpr ⟨hBr, hB⟩, ?_, ?_⟩
  · intro ξ
    calc
      _ = ∫⁻ η, ‖D.regular ξ η + (D.principal.map (fun t => t.kernel ξ η)).sum‖ₑ := by
        apply lintegral_congr_ae
        filter_upwards [volume.ae_ne ξ] with η hη
        rw [D.eq_off_diagonal ξ η hη.symm, add_comm]
      _ ≤ (∫⁻ η, ‖D.regular ξ η‖ₑ) +
          ∫⁻ η, ‖(D.principal.map (fun t => t.kernel ξ η)).sum‖ₑ :=
        row_mass_add_le _ _ (D.regular_isRegular.integrable_slices ξ).1.aestronglyMeasurable
      _ ≤ Ar + A := add_le_add (har ξ) (ha ξ)
  · intro η
    calc
      _ = ∫⁻ ξ, ‖D.regular ξ η + (D.principal.map (fun t => t.kernel ξ η)).sum‖ₑ := by
        apply lintegral_congr_ae
        filter_upwards [volume.ae_ne η] with ξ hξ
        rw [D.eq_off_diagonal ξ η hξ, add_comm]
      _ ≤ (∫⁻ ξ, ‖D.regular ξ η‖ₑ) +
          ∫⁻ ξ, ‖(D.principal.map (fun t => t.kernel ξ η)).sum‖ₑ :=
        row_mass_add_le _ _ (D.regular_isRegular.integrable_slices η).2.aestronglyMeasurable
      _ ≤ Br + B := add_le_add (hbr η) (hb η)

end RothschildStein.P1

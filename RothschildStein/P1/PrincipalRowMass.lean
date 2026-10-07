-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalRowIntegrability
public import RothschildStein.P1.FamilyChartMass

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

/-- Every actual positive-type principal term has a finite
uniform absolute row-mass bound, including endpoints outside its cutoffs. -/
theorem LiftedChart.exists_principal_row_mass_bound
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (hdegree : t.degree ≤ 1)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ ξ, (∫⁻ η, ‖t.kernel ξ η‖ₑ) ≤ A := by
  let L := tsupport t.a ∪ tsupport t.b
  have hL : IsCompact L := t.a.hasCompactSupport.union t.b.hasCompactSupport
  have hLU : L ⊆ C.U := union_subset
    (t.a.tsupport_subset.trans hVU) (t.b.tsupport_subset.trans hVU)
  have hWB := t.cutoffModelKernel_hasWeightedBounds hΓ hhom
  rw [hG] at hWB
  have hd : -(C.G.homogeneousDimension : ℤ) <
      2 - (C.G.homogeneousDimension : ℤ) - t.degree := by omega
  obtain ⟨A, hA, ha⟩ := C.exists_family_patch_mass_bound t.cutoffModelKernel _ hd hWB L hL hLU
  refine ⟨A, hA, ?_⟩
  intro ξ
  by_cases hξ : ξ ∈ L
  · have hsupp : (fun η => ‖t.kernel ξ η‖ₑ).support ⊆ L := by
      intro η hη
      apply Or.inr
      by_contra he
      have hb : t.b η = 0 := image_eq_zero_of_notMem_tsupport he
      exact hη (by simp only [PrincipalTerm.kernel, hb, mul_zero, zero_mul, enorm_zero])
    rw [← setLIntegral_eq_of_support_subset hsupp]
    have he : (fun η => t.cutoffModelKernel ξ η (C.Θ η ξ)) = t.kernel ξ := by
      funext η
      rw [t.kernel_eq_cutoffModelKernel, hΘ]
    exact (setLIntegral_congr_fun hL.measurableSet
      (fun η _ => congrArg (fun x : ℝ => ‖x‖ₑ) (congrFun he η).symm)).le.trans (ha ξ hξ)
  · have hzero : ∀ η, t.kernel ξ η = 0 := by
      intro η
      have ha : t.a ξ = 0 := image_eq_zero_of_notMem_tsupport (fun h => hξ (Or.inl h))
      simp only [PrincipalTerm.kernel, ha, zero_mul]
    simp only [hzero, enorm_zero, lintegral_zero]
    exact bot_le

end RothschildStein.P1

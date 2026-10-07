-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalReflectedKernel
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
uniform absolute column-mass bound, including endpoints outside its cutoffs. -/
theorem LiftedChart.exists_principal_column_mass_bound
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (hdegree : t.degree ≤ 1)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ ξ, (∫⁻ η, ‖t.kernel η ξ‖ₑ) ≤ A := by
  let L := tsupport t.a ∪ tsupport t.b
  have hL : IsCompact L := t.a.hasCompactSupport.union t.b.hasCompactSupport
  have hLU : L ⊆ C.U := union_subset
    (t.a.tsupport_subset.trans hVU) (t.b.tsupport_subset.trans hVU)
  have hWB := t.reflectedCutoffModelKernel_hasWeightedBounds hΓ hhom
  rw [hG] at hWB
  have hd : -(C.G.homogeneousDimension : ℤ) <
      2 - (C.G.homogeneousDimension : ℤ) - t.degree := by omega
  obtain ⟨A, hA, ha⟩ := C.exists_family_patch_mass_bound (fun ξ η u => t.cutoffModelKernel η ξ (-u)) _ hd hWB L hL hLU
  refine ⟨A, hA, ?_⟩
  intro ξ
  by_cases hξ : ξ ∈ L
  · have hsupp : (fun η => ‖t.kernel η ξ‖ₑ).support ⊆ L := by
      intro η hη
      apply Or.inl
      by_contra he
      have hb : t.a η = 0 := image_eq_zero_of_notMem_tsupport he
      exact hη (by simp only [PrincipalTerm.kernel, hb, zero_mul, enorm_zero])
    rw [← setLIntegral_eq_of_support_subset hsupp]
    have he : ∀ η ∈ L,
        t.kernel η ξ = t.cutoffModelKernel η ξ (-C.Θ η ξ) := by
      intro η hη
      rw [t.kernel_eq_cutoffModelKernel, hΘ,
        C.theta_antisymm ξ (hLU hξ) η (hLU hη)]
      rw [neg_neg]
    exact (setLIntegral_congr_fun hL.measurableSet
      (fun η hη => congrArg (fun x : ℝ => ‖x‖ₑ) (he η hη))).le.trans (ha ξ hξ)
  · have hzero : ∀ η, t.kernel η ξ = 0 := by
      intro η
      have ha : t.b ξ = 0 := image_eq_zero_of_notMem_tsupport (fun h => hξ (Or.inr h))
      simp only [PrincipalTerm.kernel, ha, mul_zero, zero_mul]
    simp only [hzero, enorm_zero, lintegral_zero]
    exact bot_le

end RothschildStein.P1

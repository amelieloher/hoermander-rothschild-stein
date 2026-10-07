-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalCutoffKernel
public import RothschildStein.P1.FamilyChartIntegrability

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Every row of an actual positive-type principal term is absolutely
integrable. The endpoint may lie outside the chart, where the output cutoff vanishes. -/
theorem LiftedChart.integrable_principal_row
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (hdegree : t.degree ≤ 1)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u)
    (ξ : Fin (n + m) → ℝ) : Integrable (t.kernel ξ) := by
  by_cases ha : t.a ξ = 0
  · have he : t.kernel ξ = fun _ => 0 := by
      funext η
      simp only [PrincipalTerm.kernel, ha, zero_mul]
    rw [he]
    exact integrable_zero _ _ volume
  · let L := tsupport t.a ∪ tsupport t.b
    have hL : IsCompact L := t.a.hasCompactSupport.union t.b.hasCompactSupport
    have hLU : L ⊆ C.U := union_subset
      (t.a.tsupport_subset.trans hVU) (t.b.tsupport_subset.trans hVU)
    have hξ : ξ ∈ L := Or.inl (subset_tsupport t.a ha)
    have hWB := t.cutoffModelKernel_hasWeightedBounds hΓ hhom
    rw [hG] at hWB
    have hd : -(C.G.homogeneousDimension : ℤ) <
        2 - (C.G.homogeneousDimension : ℤ) - t.degree := by omega
    have hint := C.integrableOn_family_comp_theta t.cutoffModelKernel _ hd
      (t.cutoffModelKernel_contDiffOn hΓ) hWB L hL hLU ξ hξ
      (tsupport t.b) t.b.hasCompactSupport (fun _ h => Or.inr h)
    have he : (fun η => t.cutoffModelKernel ξ η (C.Θ η ξ)) = t.kernel ξ := by
      funext η
      rw [t.kernel_eq_cutoffModelKernel, hΘ]
    rw [he] at hint
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp hint
    intro η hη
    apply subset_tsupport t.b
    intro hb
    apply hη
    simp only [PrincipalTerm.kernel, hb, mul_zero, zero_mul]

end RothschildStein.P1

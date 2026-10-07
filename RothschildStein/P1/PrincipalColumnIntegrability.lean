-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalRowIntegrability

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Every column of an actual positive-type principal term is absolutely
integrable, by exchanging endpoints and reflecting the model variable. -/
theorem LiftedChart.integrable_principal_column
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (hdegree : t.degree ≤ 1)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u)
    (ξ : Fin (n + m) → ℝ) : Integrable (fun η => t.kernel η ξ) := by
  by_cases hb : t.b ξ = 0
  · have he : (fun η => t.kernel η ξ) = fun _ => 0 := by
      funext η
      simp only [PrincipalTerm.kernel, hb, mul_zero, zero_mul]
    rw [he]
    exact integrable_zero _ _ volume
  · let L := tsupport t.a ∪ tsupport t.b
    have hL : IsCompact L := t.a.hasCompactSupport.union t.b.hasCompactSupport
    have hLU : L ⊆ C.U := union_subset
      (t.a.tsupport_subset.trans hVU) (t.b.tsupport_subset.trans hVU)
    have hξ : ξ ∈ L := Or.inr (subset_tsupport t.b hb)
    let Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ :=
      fun ξ η u => t.cutoffModelKernel η ξ (-u)
    have hreg : ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry Ψ) {z | z.2.2 ≠ 0} := by
      have hmap : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
            (z.2.1, z.1, -z.2.2)) :=
        contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd.neg)
      exact (t.cutoffModelKernel_contDiffOn hΓ).comp hmap.contDiffOn
        (fun z hz => neg_ne_zero.mpr hz)
    have hhomΨ : ∀ a b : Fin (n + m) → ℝ, ∀ r : ℝ, 0 < r →
        ∀ u : Fin (n + m) → ℝ, u ≠ 0 → Ψ a b (C.G.dilate r u) =
          r ^ (2 - (C.G.homogeneousDimension : ℤ) - t.degree) * Ψ a b u := by
      intro a b r hr u hu
      change t.cutoffModelKernel b a (-C.G.dilate r u) = _
      rw [← kdilate_neg, ← hG]
      have he : (((2 : ℤ) - F.G.homogeneousDimension - t.degree : ℤ) : ℝ) =
          (2 : ℝ) - F.G.homogeneousDimension - t.degree := by push_cast; rfl
      simpa only [Ψ, ← he, Real.rpow_intCast] using
        t.cutoffModelKernel_homogeneous hΓ hhom b a r hr (-u) (neg_ne_zero.mpr hu)
    have hWB : HasWeightedBounds C.G (2 - (C.G.homogeneousDimension : ℤ) - t.degree) Ψ :=
      hasWeightedBounds_of_homogeneous (hreg.of_le (by simp)) hhomΨ
    have hd : -(C.G.homogeneousDimension : ℤ) <
        2 - (C.G.homogeneousDimension : ℤ) - t.degree := by omega
    have hint := C.integrableOn_family_comp_theta Ψ _ hd hreg hWB L hL hLU ξ hξ
      (tsupport t.a) t.a.hasCompactSupport (fun _ h => Or.inl h)
    have he : EqOn (fun η => Ψ ξ η (C.Θ η ξ)) (fun η => t.kernel η ξ) (tsupport t.a) := by
      intro η hη
      change Ψ ξ η (C.Θ η ξ) = t.kernel η ξ
      rw [t.kernel_eq_cutoffModelKernel, hΘ]
      change t.cutoffModelKernel η ξ (-C.Θ η ξ) = t.cutoffModelKernel η ξ (C.Θ ξ η)
      rw [C.theta_antisymm η (hLU (Or.inl hη)) ξ (hLU hξ)]
    have hint' := hint.congr_fun he t.a.hasCompactSupport.measurableSet
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp hint'
    intro η hη
    apply subset_tsupport t.a
    intro ha
    apply hη
    simp only [PrincipalTerm.kernel, ha, zero_mul]

end RothschildStein.P1

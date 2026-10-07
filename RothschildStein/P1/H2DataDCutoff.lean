-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2DataDMeasurable
public import RothschildStein.H2.LocalizedKernelDefs

/-!
# The localization cutoffs as H2 kernel cutoffs

The finite localization (`IsLocalization`) provides Euclidean-smooth
cutoffs `χ_j, ψ_j` on `ℝ^{n+m}` with compact support in `U`. H2's `KernelCutoff (ball z R) L a`
asks for a `[0,1]`-valued function on the carrier which is `L`-Lipschitz for the lifted control
metric `d̃` and vanishes outside the ball. A finite Lipschitz constant exists: near the support a
smooth function is `d̃`-Lipschitz by integrating its derivative along a controlled curve
(`exists_lipschitz_first`), and away
from the support the distance `d̃` to the support is bounded below, so the sup bound `1` is
controlled by `d̃/δ` (BB Def. 7.9, p. 299).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- A `[0,1]`-valued smooth function with compact support in the
chart domain `U` is Lipschitz on the carrier for the lifted control distance `d̃`. -/
theorem exists_lipschitzWith_comp_val {χ : (Fin (n + m) → ℝ) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (h01 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1)
    (hc : IsCompact (tsupport χ)) (hU : tsupport χ ⊆ C.U) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x : C.Carrier => χ x.val) := by
  obtain ⟨δe, hδe, hLU⟩ := hc.exists_cthickening_subset_open C.isOpen_U hU
  have hLc : IsCompact (cthickening δe (tsupport χ)) := hc.cthickening
  set K' : Set C.Carrier := Carrier.val ⁻¹' tsupport χ with hK'
  set L' : Set C.Carrier := Carrier.val ⁻¹' cthickening δe (tsupport χ) with hL'
  have hK'c : IsCompact K' := Carrier.isCompact_preimage_val hc hU
  have hL'c : IsCompact L' := Carrier.isCompact_preimage_val hLc hLU
  have hKint : K' ⊆ interior L' := by
    have h1 : (Carrier.val ⁻¹' thickening δe (tsupport χ) : Set C.Carrier) ⊆ interior L' :=
      interior_maximal (preimage_mono (thickening_subset_cthickening δe _))
        (isOpen_thickening.preimage Carrier.continuous_val)
    exact (preimage_mono (self_subset_thickening hδe _)).trans h1
  obtain ⟨δ, hδ, hcth⟩ := hK'c.exists_cthickening_subset_open isOpen_interior hKint
  have hLimg : IsCompact (Carrier.val '' L' : Set (Fin (n + m) → ℝ)) :=
    hL'c.image Carrier.continuous_val
  have hLimgU : Carrier.val '' L' ⊆ C.U := by
    rintro _ ⟨x, -, rfl⟩
    exact x.val_mem
  have hG : ContDiffOn ℝ 1 (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => χ p.1)
      (C.U ×ˢ C.U) :=
    (hχ.comp contDiff_fst).contDiffOn.of_le (by simp)
  obtain ⟨M, hM0, hM⟩ := C.exists_lipschitz_first hG hLimg hLimgU
  have hδinv : 0 ≤ 1 / δ := by positivity
  have key : ∀ x y : C.Carrier, x ∈ K' → |χ x.val - χ y.val| ≤ (M + 1 / δ) * dist x y := by
    intro x y hx
    by_cases hxy : dist x y < δ
    · have hxL : x ∈ L' := interior_subset (hKint hx)
      have hyL : y ∈ L' := interior_subset (hcth
        (Metric.mem_cthickening_of_dist_le y x δ K' hx (by rw [dist_comm]; exact hxy.le)))
      have h1 : |χ y.val - χ x.val| ≤ M * (C.dl x.val y.val).toReal :=
        hM x.val ⟨x, hxL, rfl⟩ y.val ⟨y, hyL, rfl⟩ x.val ⟨x, hxL, rfl⟩
      have h2 : (C.dl x.val y.val).toReal = dist x y := rfl
      rw [h2] at h1
      rw [abs_sub_comm]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hδinv) dist_nonneg)
    · have hge : δ ≤ dist x y := not_lt.mp hxy
      have h01x := h01 x.val
      have h01y := h01 y.val
      have h1 : |χ x.val - χ y.val| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [h01x.1, h01x.2, h01y.1, h01y.2]
      have h2 : 1 ≤ (1 / δ) * dist x y := by
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hδ]
        linarith
      calc |χ x.val - χ y.val| ≤ 1 := h1
        _ ≤ (1 / δ) * dist x y := h2
        _ ≤ (M + 1 / δ) * dist x y :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM0) dist_nonneg
  refine ⟨⟨M + 1 / δ, add_nonneg hM0 hδinv⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.dist_eq]
  by_cases hx : x ∈ K'
  · exact key x y hx
  · by_cases hy : y ∈ K'
    · rw [abs_sub_comm, dist_comm x y]
      exact key y x hy
    · have h1 : χ x.val = 0 := image_eq_zero_of_notMem_tsupport hx
      have h2 : χ y.val = 0 := image_eq_zero_of_notMem_tsupport hy
      rw [h1, h2, sub_self, abs_zero]
      exact mul_nonneg (add_nonneg hM0 hδinv) dist_nonneg

namespace IsLocalization

variable {S : H2.LocDoubling C.Carrier} {F : Set (Fin (n + m) → ℝ)} {r : ℝ}
  {t : Finset C.Carrier} {χ ψ : C.Carrier → (Fin (n + m) → ℝ) → ℝ}

/-- The cutoff `χ_j ∘ val` is an H2 kernel cutoff on `ball z_j r`:
`[0,1]`-valued, Lipschitz for the lifted control distance and supported in `B(z_j, r/4)`. -/
theorem exists_kernelCutoff_χ (h : C.IsLocalization S F r t χ ψ) (hr : 0 < r) {z : C.Carrier}
    (hz : z ∈ t) :
    ∃ L : ℝ≥0, H2.KernelCutoff (ball z r) L (fun x : C.Carrier => χ z x.val) := by
  have hU : tsupport (χ z) ⊆ C.U := by
    intro ξ hξ
    obtain ⟨y, -, rfl⟩ := h.χ_support z hz hξ
    exact y.val_mem
  obtain ⟨L, hL⟩ := exists_lipschitzWith_comp_val (h.χ_smooth z hz) (h.χ_mem z hz)
    (h.χ_compact z hz) hU
  refine ⟨L, hL, fun x => (h.χ_mem z hz x.val).1, fun x => (h.χ_mem z hz x.val).2, ?_⟩
  intro x hx
  by_contra hne
  have hmem : x.val ∈ tsupport (χ z) := subset_tsupport _ (Function.mem_support.mpr hne)
  obtain ⟨y, hy, hyx⟩ := h.χ_support z hz hmem
  have hyx' : y = x := Carrier.val_injective hyx
  subst hyx'
  exact hx (ball_subset_ball (by linarith) hy)

/-- The cutoff `ψ_j ∘ val` is an H2 kernel cutoff on `ball z_j r`:
`[0,1]`-valued, Lipschitz for the lifted control distance and supported in `B(z_j, r)`. -/
theorem exists_kernelCutoff_ψ (h : C.IsLocalization S F r t χ ψ) {z : C.Carrier} (hz : z ∈ t) :
    ∃ L : ℝ≥0, H2.KernelCutoff (ball z r) L (fun x : C.Carrier => ψ z x.val) := by
  have hU : tsupport (ψ z) ⊆ C.U := by
    intro ξ hξ
    obtain ⟨y, -, rfl⟩ := h.ψ_support z hz hξ
    exact y.val_mem
  obtain ⟨L, hL⟩ := exists_lipschitzWith_comp_val (h.ψ_smooth z hz) (h.ψ_mem z hz)
    (h.ψ_compact z hz) hU
  refine ⟨L, hL, fun x => (h.ψ_mem z hz x.val).1, fun x => (h.ψ_mem z hz x.val).2, ?_⟩
  intro x hx
  by_contra hne
  have hmem : x.val ∈ tsupport (ψ z) := subset_tsupport _ (Function.mem_support.mpr hne)
  obtain ⟨y, hy, hyx⟩ := h.ψ_support z hz hmem
  have hyx' : y = x := Carrier.val_injective hyx
  subst hyx'
  exact hx hy

end IsLocalization

end LiftedChart
end RothschildStein.P1

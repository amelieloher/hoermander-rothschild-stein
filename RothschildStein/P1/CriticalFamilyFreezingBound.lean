-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.JointChartInverseBound
public import RothschildStein.P1.SingularSplitEstimatesHadamard
public import RothschildStein.P1.KernelEstimatesWeightedTaylor

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Freezing the second endpoint of the actual
critical operator family leaves an integrable pole of order 1−Q,
uniformly on compact center patches. -/
theorem exists_criticalFamily_freezing_bound
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 ≤ M ∧ ∀ ξ ∈ K, ∀ u, u ≠ 0 → kgauge C.G u ≤ ε →
      ‖(D ξ ((C.e ξ).symm (-u))).apply Γ u - (D ξ ξ).apply Γ u‖ ≤
        M * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℤ)) := by
  classical
  obtain ⟨ρ, A, hρ, hA, hI⟩ := exists_inverse_zero_bound hK hKU
  let S := K ×ˢ closedBall (0 : Fin (n + m) → ℝ) ρ
  let I := fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.e p.1).symm (-p.2)
  have hmap : MapsTo (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p.1, -p.2)) S C.T := by
    intro p hp
    have hn : ‖-p.2‖ ≤ ρ := by simpa using hp.2
    exact ⟨hKU hp.1, (hI p.1 hp.1 (-p.2) hn).1⟩
  have hIc : IsCompact (I '' S) := (hK.prod (isCompact_closedBall (0 : Fin (n + m) → ℝ) ρ)).image_of_continuousOn
    (C.inverse_joint_contDiffOn.continuousOn.comp
      (continuous_fst.prodMk continuous_snd.neg).continuousOn hmap)
  let L := K ∪ I '' S
  have hL : IsCompact L := hK.union hIc
  have hV (l : Fin (n + m)) : HasWeightedBounds C.G (-(C.G.homogeneousDimension : ℤ))
      (fun ξ η u => F.hadamardKernel Γ l ξ η u) := by
    apply hasWeightedBounds_of_homogeneous
      ((F.contDiffOn_kernelUncurry_hadamard hΓ l).of_le (by simp))
    intro ξ η r hr u hu
    simpa only [Nat.cast_zero, zero_sub] using F.hadamardKernel_dilate Γ hΓ hhom l ξ η hr hu
  choose B hB hb using fun l : Fin (n + m) => hV l L hL 1
  refine ⟨min ρ 1, A * ∑ l, B l, lt_min hρ one_pos,
    mul_nonneg hA (Finset.sum_nonneg (fun l _ => hB l)), ?_⟩
  intro ξ hξ u hu hε
  have hsmall : kgauge C.G u ≤ 1 := hε.trans (min_le_right _ _)
  have hn : ‖-u‖ ≤ ρ := by
    simpa only [norm_neg] using (norm_le_kgauge C.G hsmall).trans (hε.trans (min_le_left _ _))
  let η := (C.e ξ).symm (-u)
  have hη : η ∈ L := Or.inr ⟨(ξ, u), ⟨hξ, by simpa only [mem_closedBall, dist_zero_right, norm_neg] using hn⟩, rfl⟩
  have hξL : ξ ∈ L := Or.inl hξ
  have hd : ‖η - ξ‖ ≤ A * kgauge C.G u :=
    (hI ξ hξ (-u) hn).2.trans (by
      simpa only [norm_neg] using mul_le_mul_of_nonneg_left (norm_le_kgauge C.G hsmall) hA)
  rw [F.apply_sub_eq_sum]
  calc
    ‖∑ l, (η l - ξ l) * F.hadamardKernel Γ l ξ η u‖ ≤
        ∑ l, ‖(η l - ξ l) * F.hadamardKernel Γ l ξ η u‖ := norm_sum_le _ _
    _ ≤ ∑ l, (A * B l) * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℤ)) := by
      apply Finset.sum_le_sum
      intro l _
      have hcoord : ‖η l - ξ l‖ ≤ A * kgauge C.G u := (norm_le_pi_norm (η - ξ) l).trans hd
      have hk : ‖F.hadamardKernel Γ l ξ η u‖ ≤
          B l * kgauge C.G u ^ (-(C.G.homogeneousDimension : ℤ)) := by
        simpa only [Real.norm_eq_abs] using (hb l ξ hξL η hη u hu hsmall).1
      rw [norm_mul]
      calc
        ‖η l - ξ l‖ * ‖F.hadamardKernel Γ l ξ η u‖ ≤
            (A * kgauge C.G u) * (B l * kgauge C.G u ^ (-(C.G.homogeneousDimension : ℤ))) :=
          mul_le_mul hcoord hk (norm_nonneg _) (mul_nonneg hA (kgauge_nonneg C.G u))
        _ = (A * B l) * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℤ)) := by
          rw [sub_eq_add_neg, zpow_add₀ (kgauge_pos C.G hu).ne', zpow_one]
          ring
    _ = (A * ∑ l, B l) * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℤ)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

end RothschildStein.P1.LiftedChart

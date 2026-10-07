-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.HomogeneousFamilyGaugeBound
public import RothschildStein.P1.CompactParameterMeanValue
public import RothschildStein.G2.EuclideanComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
variable {N : ℕ}

/-- The uniform subtracted critical bound holds
for the prescribed homogeneous gauge, with its local norm comparison. -/
theorem exists_uniformGaugeCriticalTest_near_bound
    (G : HomogeneousGroup N) {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hc : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η, ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ (-(G.homogeneousDimension : ℝ)) * Ψ ξ η u)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (ψ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (U ×ˢ (univ : Set (Fin N → ℝ))))
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ K, ∀ u, u ≠ 0 → ν u ≤ 1 →
      ‖Ψ ξ ξ u * (ψ (ξ, u) - ψ (ξ, 0))‖ ≤
        M * ν u ^ (1 - (G.homogeneousDimension : ℝ)) := by
  obtain ⟨A, hA, ha⟩ := exists_homogeneousFamily_gauge_bound G hν Ψ hc hhom hK
  obtain ⟨a, b, ha0, _, hnorm⟩ := G2.gauge_sublevel_norm_comparison hν 1
  obtain ⟨B, hB, hb⟩ := exists_compactParameter_model_sub_bound hU ψ hψ hK hKU
    (show (0 : ℝ) ≤ 1 / a by positivity)
  refine ⟨A * (B / a), mul_nonneg hA (div_nonneg hB ha0.le), ?_⟩
  intro ξ hξ u hu hρ
  have huNorm : ‖u‖ ≤ ν u / a := by
    rw [le_div_iff₀ ha0]
    simpa only [mul_comm] using (hnorm u hρ).1
  have ht : ‖ψ (ξ, u) - ψ (ξ, 0)‖ ≤ (B / a) * ν u := by
    have hr : ‖u‖ ≤ 1 / a := huNorm.trans (div_le_div_of_nonneg_right hρ ha0.le)
    calc
      ‖ψ (ξ, u) - ψ (ξ, 0)‖ ≤ B * ‖u‖ := hb ξ hξ u hr
      _ ≤ B * (ν u / a) := mul_le_mul_of_nonneg_left huNorm hB
      _ = (B / a) * ν u := by ring
  rw [norm_mul]
  have hp : 0 < ν u := lt_of_le_of_ne (hν.2.1 u)
    (Ne.symm (fun hz => hu ((hν.2.2.1 u).mp hz)))
  calc
    ‖Ψ ξ ξ u‖ * ‖ψ (ξ, u) - ψ (ξ, 0)‖ ≤
        (A * ν u ^ (-(G.homogeneousDimension : ℝ))) * ((B / a) * ν u) :=
      mul_le_mul (ha ξ hξ ξ hξ u hu) ht (norm_nonneg _)
        (mul_nonneg hA (Real.rpow_nonneg hp.le _))
    _ = (A * (B / a)) * ν u ^ (1 - (G.homogeneousDimension : ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hp, Real.rpow_one]
      ring

end RothschildStein.P1

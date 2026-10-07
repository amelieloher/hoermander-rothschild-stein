-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalProductFactorization

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace RothschildStein.G1

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Local signed factors can be extended smoothly with a common
cut-off which is one near the reference point and preserves opposite
zero-time coefficients (BB Thm 1.48, pp. 32–34). -/
theorem exists_signedFactor_localExtensions {U : Set (P × E)} (hU : IsOpen U)
    (Hp Hm : P × E → E) (hHp : ContDiffOn ℝ (⊤ : ℕ∞) Hp U)
    (hHm : ContDiffOn ℝ (⊤ : ℕ∞) Hm U)
    (hmatch : ∀ x, (0, x) ∈ U → -Hm (0, x) = Hp (0, x))
    (x : E) (hx : (0, x) ∈ U) :
    ∃ Kp Km : P × E → E, ContDiff ℝ (⊤ : ℕ∞) Kp ∧ ContDiff ℝ (⊤ : ℕ∞) Km ∧
      (∀ y, -Km (0, y) = Kp (0, y)) ∧
      ∀ᶠ q in 𝓝 ((0 : P), x), Kp q = Hp q ∧ Km q = Hm q := by
  obtain ⟨φ, hsupp, _, hφ, _, hφx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
  let b : ContDiffBump (1 : ℝ) :=
    ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let η : P × E → ℝ := fun q => b (φ q)
  have hb0 : b (0 : ℝ) = 0 := b.zero_of_le_dist (by norm_num [b, Real.dist_eq])
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := b.contDiff.comp hφ
  have hsη : tsupport η ⊆ U := by
    apply Subset.trans (closure_mono (t := Function.support φ) ?_) hsupp
    intro q hq
    change η q ≠ 0 at hq
    change φ q ≠ 0
    intro hz
    apply hq
    dsimp [η]
    rw [hz, hb0]
  have he : ∀ᶠ q in 𝓝 ((0 : P), x), η q = 1 := by
    have hb : ∀ᶠ t : ℝ in 𝓝 (φ (0, x)), b t = 1 := by
      rw [hφx]
      filter_upwards [b.eventuallyEq_one] with t ht
      exact ht
    exact (hφ.continuous.tendsto (0, x)).eventually hb
  refine ⟨fun q => η q • Hp q, fun q => η q • Hm q,
    cutoff_smul_contDiff hU Hp hHp η hη hsη,
    cutoff_smul_contDiff hU Hm hHm η hη hsη, ?_, ?_⟩
  · intro y
    by_cases hy : η (0, y) = 0
    · simp only [hy, zero_smul, neg_zero]
    · have hmem : (0, y) ∈ U := hsη (subset_closure hy)
      rw [← smul_neg, hmatch y hmem]
  · filter_upwards [he] with q hq
    simp only [hq, one_smul, and_self]

end RothschildStein.G1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactMollifierConvergence
public import RothschildStein.Definitions.memSobolevXZero
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Function
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compact interior Sobolev data satisfy the exact zero-boundary predicate, with explicit ordinary mollifications as tests
(BB Cor 2.10, p. 73; Prop 8.49, p. 379). -/
theorem memSobolevXZero_of_compact_support
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (hpt : p ≠ ⊤) {f : (Fin n → ℝ) → ℝ}
    (hf : memSobolevX w X Ω k p f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ω) : memSobolevXZero w X Ω k p f := by
  have hi : (Ω : Set (Fin n → ℝ)).indicator f = f := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))).symm
  have hl : LocallyIntegrable f volume := by
    have H := (memLp_zeroExtension_iff Ω.isOpen.measurableSet f).mpr hf.1
    rw [hi] at H
    exact H.locallyIntegrable Fact.out
  obtain ⟨δ,hd,hδ⟩ := exists_euclideanRegularize_support_inside_all_dimensions hc Ω.isOpen hs
  let ε : ℕ → ℝ := fun j => δ / ((j : ℝ)+1)
  have he (j : ℕ) : 0 < ε j := div_pos hd (by positivity)
  have hb (j : ℕ) : ε j ≤ δ := div_le_self hd.le (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
  let φ : ℕ → TestFunction Ω ℝ (⊤ : ℕ∞) := fun j =>
    ⟨euclideanRegularize n f (ε j),
      (euclideanRegularize_smooth_compact_all_dimensions hl hc (he j)).1,
      (euclideanRegularize_smooth_compact_all_dimensions hl hc (he j)).2,
      hδ (ε j) (he j) (hb j)⟩
  refine ⟨hf,φ,?_⟩
  have ht : Tendsto ε atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall he⟩
    simpa only [mul_zero,mul_one_div] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
          Tendsto (fun j : ℕ => δ * (1 / ((j : ℝ)+1))) atTop (𝓝 (δ*0)))
  exact (tendsto_sobolevXENorm_mollifier_compact w X Ω hX k hpt hf hc hs).comp ht

end RothschildStein.S

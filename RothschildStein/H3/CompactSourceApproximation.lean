-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactSourceRepresentative
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Smooth source approximation with one fixed enlarged support radius. -/
theorem exists_smooth_source_approximation (ν : G2.HomogeneousNorm G)
    (hν : ν.c = 1) {σ p : ℝ} (hp : 1 ≤ p)
    {f : (Fin N → ℝ) → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hs : ∀ᵐ x, σ ≤ ν x → f x = 0) :
    ∃ fn : ℕ → (Fin N → ℝ) → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fn j) ∧ HasCompactSupport (fn j) ∧
        ∀ x, σ + 1 ≤ ν x → fn j x = 0) ∧
      Tendsto (fun j => eLpNorm (fn j - f) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  obtain ⟨g, hg, hcg, heq, hsg⟩ := exists_compact_source_representative ν hf hs
  obtain ⟨φ⟩ := G2.nonempty_groupMollifier G ν
  obtain ⟨hreg, hlim⟩ := compact_source_regularization G φ hν hp hg hcg hsg
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hpos : ∀ j, 0 < ε j := by intro j; dsimp [ε]; positivity
  have hle : ∀ j, ε j ≤ 1 := by
    intro j
    dsimp [ε]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have ht : Tendsto ε atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hpos⟩
  refine ⟨fun j => G2.groupRegularize G φ g (ε j),
    fun j => hreg (ε j) (hpos j) (hle j), ?_⟩
  have he (j : ℕ) :
      eLpNorm (G2.groupRegularize G φ g (ε j) - g) (ENNReal.ofReal p) volume =
      eLpNorm (G2.groupRegularize G φ g (ε j) - f) (ENNReal.ofReal p) volume :=
    eLpNorm_congr_ae (EventuallyEq.sub ae_eq_rfl heq)
  exact (hlim.comp ht).congr' (Eventually.of_forall he)

end RothschildStein.H3

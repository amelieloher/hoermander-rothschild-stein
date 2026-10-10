-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LevelTruncation
public import HeatKernel.Form.ZeroBoundaryContractions
import Mathlib.Tactic.Linter

/-! # Level truncations in the zero-boundary horizontal form domain

The scalar truncation is a normal contraction. Uniqueness of the closed-form
representative combines preservation of the zero-boundary domain with the
horizontal energy bound of normal contractions.
-/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel.Sobolev

/-- The height-limited absolute-value truncation is a scalar normal contraction. -/
theorem lipschitzWith_levelTruncation (t : ℝ) :
    LipschitzWith 1 (fun s : ℝ => min (max (|s| - t) 0) t) := by
  have h : LipschitzWith 1 (fun s : ℝ => |s| - t) := by
    apply LipschitzWith.of_dist_le_mul
    intro s z
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul] using
      abs_abs_sub_abs_le_abs_sub s z
  exact (h.max_const 0).min_const t

/-- A nonnegative level makes the scalar truncation fix zero. -/
theorem levelTruncation_zero {t : ℝ} (ht : 0 ≤ t) :
    min (max (|(0 : ℝ)| - t) 0) t = 0 := by
  simp only [abs_zero, zero_sub, max_eq_right (neg_nonpos.mpr ht), min_eq_left ht]

/-- Level truncation preserves zero boundary and decreases both horizontal and graph energy. -/
theorem exists_zeroBoundaryGraph_levelTruncation {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : zeroBoundaryGraph U X) {t : ℝ} (ht : 0 ≤ t) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X ∧
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        levelTruncation (v : GradientSpace (N := N) ⊤ q).fst t ∧
      horizontalEnergy ⊤ X z z ≤ horizontalEnergy ⊤ X
        ⟨v, zeroBoundaryGraph_le_energyGraph U X v.property⟩
        ⟨v, zeroBoundaryGraph_le_energyGraph U X v.property⟩ ∧
      ‖z‖ ≤ ‖(v : GradientSpace (N := N) ⊤ q)‖ := by
  let e : energyGraph (N := N) ⊤ X :=
    ⟨v, zeroBoundaryGraph_le_energyGraph U X v.property⟩
  let η : ℝ → ℝ := fun s => min (max (|s| - t) 0) t
  have hη : LipschitzWith 1 η := lipschitzWith_levelTruncation t
  have hzero : η 0 = 0 := levelTruncation_zero ht
  obtain ⟨z, hz, he⟩ := exists_energyGraph_comp_normalContraction X hX e hη hzero
  obtain ⟨w, hw, hwe⟩ := exists_zeroBoundaryGraph_comp_normalContraction U X hX v hη hzero
  have hzw : z = w := energyInclusion_injective ⊤ X
    (fun i => (hX i).contDiffOn) (hz.trans hwe.symm)
  refine ⟨z, hzw.symm ▸ hw, ?_, he, ?_⟩
  · change (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun x => min (max (|(v : GradientSpace (N := N) ⊤ q).fst x| - t) 0) t)
    have H := hη.coeFn_compLp hzero (energyInclusion ⊤ X e)
    rw [← hz] at H
    change (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict
      ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))]
      η ∘ (e : GradientSpace (N := N) ⊤ q).fst at H
    simpa only [Opens.coe_top, Measure.restrict_univ,
      Function.comp_def, η, e] using H
  · change ‖z‖ ≤ ‖e‖
    apply energyGraph_norm_le_of_bounds ⊤ X z e _ he
    rw [hz]
    exact norm_compLp_normalContraction_le hη hzero _

end HeatKernel.Sobolev

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ReductionValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The universal model has a finite jet budget depending only on
its dimensions, order, value bound and nondegeneracy bound. Actual vector
fields do not enter this statement (BB Lemma 9.31, pp. 422–423). -/
theorem exists_valueReduction_jet_bound (p n h : ℕ) (H Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : Fin p,
      HasJetBound {u : ReductionValues p n | valueDenominator u ≠ 0}
        (Metric.closedBall 0 H ∩ {u | Δ ^ 2 ≤ valueDenominator u})
        (valueReduction J) h C := by
  classical
  let D : Set (ReductionValues p n) := {u | valueDenominator u ≠ 0}
  let K : Set (ReductionValues p n) := Metric.closedBall 0 H ∩
    {u | Δ ^ 2 ≤ valueDenominator u}
  have hD : IsOpen D := valueDenominator_domain_isOpen
  have hK : IsCompact K := valueSet_isCompact H Δ
  have hKD : K ⊆ D := by
    intro u hu
    exact ne_of_gt ((sq_pos_of_pos hΔ).trans_le hu.2)
  have hex : ∀ J : Fin p, ∀ j : Fin (h + 1), ∃ C : ℝ, ∀ u ∈ K,
      ‖iteratedFDerivWithin ℝ j.val (valueReduction J) D u‖ ≤ C := by
    intro J j
    have hc := (valueReduction_contDiffOn J).continuousOn_iteratedFDerivWithin
      (m := j.val) (by simp) hD.uniqueDiffOn
    obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (hc.mono hKD)).isBounded.exists_norm_le
    exact ⟨C, fun u hu => hC _ (mem_image_of_mem _ hu)⟩
  choose C hC using hex
  let B := 1 + ∑ J : Fin p, ∑ j : Fin (h + 1), |C J j|
  have hsum : 0 ≤ ∑ J : Fin p, ∑ j : Fin (h + 1), |C J j| := by positivity
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro J j hj u hu
  let j' : Fin (h + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have h₁ : |C J j'| ≤ ∑ k : Fin (h + 1), |C J k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (C J k)) (Finset.mem_univ j')
  have h₂ : (∑ k : Fin (h + 1), |C J k|) ≤ ∑ I : Fin p, ∑ k : Fin (h + 1), |C I k| :=
    Finset.single_le_sum (fun I _ => Finset.sum_nonneg (fun k _ => abs_nonneg (C I k)))
      (Finset.mem_univ J)
  have hb := hC J j' u hu
  dsimp [B]
  exact (hb.trans (le_abs_self _) |>.trans h₁ |>.trans h₂).trans (by linarith)

end RothschildStein.G4

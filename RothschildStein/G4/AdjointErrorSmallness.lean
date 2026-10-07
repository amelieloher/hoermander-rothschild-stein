-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedTaylorSmallness
public import RothschildStein.G1.MixedJetTimeScale

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- A finite positive-order adjoint polynomial and its positive
order remainder are simultaneously small on one coefficient interval,
with a prescribed upper radius chosen before the actual fields and frame. -/
theorem exists_adjoint_error_smallness (q N : ℕ) (hN : 0 < N)
    (c : Fin q → ℝ) (A κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ δ ∧ ∀ e : ℝ, 0 ≤ e → e ≤ ε →
      (∑ j : Fin q, c j * e ^ (j.val + 1)) + A * e ^ N < κ := by
  classical
  let P : ℝ → ℝ := fun e => (∑ j : Fin q, c j * e ^ (j.val + 1)) + A * e ^ N
  have hP : Continuous P := by
    apply Continuous.add
    · apply continuous_finsetSum
      intro j hj
      exact continuous_const.mul (continuous_id.pow (j.val + 1))
    · exact continuous_const.mul (continuous_id.pow N)
  have hP0 : P 0 = 0 := by simp [P, hN.ne']
  have hn : {e : ℝ | P e < κ} ∈ 𝓝 0 :=
    hP.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds (by rw [hP0]; exact hκ))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hn
  let ε := min (min ρ δ) 1 / 2
  have hmin : 0 < min (min ρ δ) 1 := lt_min (lt_min hρ hδ) zero_lt_one
  have hε : 0 < ε := half_pos hmin
  have hερ : ε < ρ := (half_lt_self hmin).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ : ε ≤ δ := (half_lt_self hmin).le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := (half_lt_self hmin).le.trans (min_le_right _ _)
  refine ⟨ε, hε, hε1, hεδ, ?_⟩
  intro e he heε
  exact hball (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg he]
    using heε.trans_lt hερ)

/-- One numerical radius controls both the finite weighted error
and the actual-flow jet bootstrap rate; all smaller nonnegative radii work. -/
theorem exists_adjoint_error_and_jet_smallness (q N R : ℕ) (hN : 0 < N)
    (c : Fin q → ℝ) (A B κ δ : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ δ ∧ ∀ e : ℝ, 0 ≤ e → e ≤ ε →
      ((∑ j : Fin q, c j * e ^ (j.val + 1)) + A * e ^ N < κ) ∧
        G1.spatialJetRate R (B * e) < 1 := by
  let L := G1.spatialJetRate R B
  have hL : 0 ≤ L := by
    dsimp [L, G1.spatialJetRate]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  let η := min δ (1 / (2 * (1 + L)))
  have hη : 0 < η := lt_min hδ (by positivity)
  obtain ⟨ε, hε, hε1, hεη, hsmall⟩ := exists_adjoint_error_smallness q N hN c A κ η hκ hη
  refine ⟨ε, hε, hε1, hεη.trans (min_le_left _ _), ?_⟩
  intro e he heε
  refine ⟨hsmall e he heε, ?_⟩
  have heη : e ≤ 1 / (2 * (1 + L)) :=
    (heε.trans hεη).trans (min_le_right _ _)
  have hprod : e * (2 * (1 + L)) ≤ 1 := (le_div_iff₀ (by positivity)).mp heη
  rw [mul_comm B e, G1.spatialJetRate_mul_left]
  change e * L < 1
  nlinarith

end RothschildStein.G4

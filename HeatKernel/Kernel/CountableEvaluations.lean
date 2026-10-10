-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.RepresentativeKernelRegularity
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.Bases

/-! # Countable Hilbert bases and measurable evaluation kernels

Disjoint small balls around an orthonormal family show that its index set is
countable in a separable real Hilbert space. Lebesgue L² is separable, so scalar
continuity suffices for joint measurability without choosing a basis as input.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- An orthonormal family in a separable real Hilbert space has a countable index type. -/
theorem countable_of_orthonormal {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [TopologicalSpace.SeparableSpace H]
    {v : ι → H} (hv : Orthonormal ℝ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1 / 2))
      (Metric.ball (v j) (1 / 2))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hsq : dist (v i) (v j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real, hv.norm_eq_one i, hv.norm_eq_one j,
        hv.inner_eq_zero hij]
      norm_num
    have hdist : dist (v i) (v j) < 1 := by
      have hi : dist (v i) z < 1 / 2 := by simpa only [Metric.mem_ball, dist_comm] using hzi
      have hj : dist z (v j) < 1 / 2 := hzj
      linarith [dist_triangle (v i) z (v j)]
    have hmul := mul_le_mul_of_nonneg_left hdist.le (dist_nonneg (x := v i) (y := v j))
    nlinarith [hmul]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

/-- Continuous positive-time Lebesgue L² representatives determine a jointly measurable kernel. -/
theorem measurable_heatRepresentativeKernel {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hjoint : ∀ f, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2)
      {p | 0 < p.1}) :
    Measurable (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 p.2.1 p.2.2) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ (Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
  let : Countable w := countable_of_orthonormal b.orthonormal
  exact measurable_heatRepresentativeKernel_of_basis T u hu hae b hjoint

end HeatKernel

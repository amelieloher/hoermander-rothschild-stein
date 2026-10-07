-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.MaximalBasic
public import RothschildStein.H2.DifferentiationConsequences
public import RothschildStein.H2.Vitali

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Metric MeasureTheory Function
open scoped ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Summing the large-average inequalities over the disjoint Vitali balls. -/
theorem disjoint_large_average_sum_le {ι : Type*} [Countable ι]
    (μ : Measure X) (W : Set X) (f : X → ℝ) (z : ι → X) (r : ι → ℝ)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htt : t ≠ ⊤)
    (hdisj : Pairwise (Disjoint on (fun i => ball (z i) (r i))))
    (hinside : ∀ i, ball (z i) (r i) ⊆ W)
    (hpos : ∀ i, 0 < μ (ball (z i) (r i)))
    (hfinite : ∀ i, μ (ball (z i) (r i)) ≠ ⊤)
    (havg : ∀ i, t < ⨍⁻ y in ball (z i) (r i), ‖f y‖ₑ ∂μ)
    (hf : IntegrableOn f W μ) :
    (∑' i, μ (ball (z i) (r i))) ≤ eLpNorm f 1 (μ.restrict W) / t := by
  have hle (i : ι) : μ (ball (z i) (r i)) ≤
      (∫⁻ y in ball (z i) (r i), ‖f y‖ₑ ∂μ) / t := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl htt)).mpr
    rw [mul_comm]
    have hi := (havg i).le
    rw [setLAverage_eq] at hi
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hpos i).ne') (Or.inl (hfinite i))).mp hi
  calc
    (∑' i, μ (ball (z i) (r i))) ≤
        ∑' i, (∫⁻ y in ball (z i) (r i), ‖f y‖ₑ ∂μ) / t := ENNReal.tsum_le_tsum hle
    _ = (∑' i, ∫⁻ y in ball (z i) (r i), ‖f y‖ₑ ∂μ) / t := by
      simp only [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ = (∫⁻ y in ⋃ i, ball (z i) (r i), ‖f y‖ₑ ∂μ) / t := by
      rw [lintegral_iUnion (fun _ => isOpen_ball.measurableSet) hdisj]
    _ ≤ (∫⁻ y in W, ‖f y‖ₑ ∂μ) / t := by
      gcongr
      exact iUnion_subset hinside
    _ = _ := by rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]

/-- The weak (1,1) estimate with constant C_D cubed for
explicit patch clauses P1–P3 (BB Theorem 7.25, pp. 313–314). -/
theorem patchMaximal_weak_type
    (μ : Measure X) (S W : Set X) (ρ C : ℝ) (hρ : 0 < ρ) (hC : 1 < C)
    (hinside : ∀ z ∈ S, ball z (6 * ρ) ⊆ W)
    (hballs : ∀ z ∈ S, ∀ s : ℝ, 0 < s → s ≤ 6 * ρ →
      0 < μ (ball z s) ∧ μ (ball z s) < ⊤ ∧
        μ (ball z s) ≤ ENNReal.ofReal C * μ (ball z (s / 2)))
    (hW : MeasurableSet W ∧ μ W < ⊤) : PatchMaximalWeakType μ S W ρ C := by
  intro f hf t ht
  let T := {i : X × ℝ | i.1 ∈ S ∧ i.2 ∈ Ioc 0 ρ ∧
    ENNReal.ofReal t < ⨍⁻ y in ball i.1 i.2, ‖f y‖ₑ ∂μ}
  obtain ⟨u, huT, hcount, hdisj, _, hmeasure⟩ :=
    vitali_covering_of_patch_hypotheses μ S W ρ C hρ hC hinside hballs hW
      T Prod.fst Prod.snd (fun i hi => hi.1) (fun i hi => hi.2.1)
  let : Countable u := hcount.to_subtype
  have hsum := disjoint_large_average_sum_le μ W f (fun i : u => i.val.1)
    (fun i : u => i.val.2) (ENNReal.ofReal t) (ENNReal.ofReal_pos.mpr ht).ne'
    ENNReal.ofReal_ne_top (hdisj.subtype _ _)
    (fun i => (ball_subset_ball (by linarith [(huT i.property).2.1.2])).trans
      (hinside i.val.1 (huT i.property).1))
    (fun i => (hballs i.val.1 (huT i.property).1 i.val.2 (huT i.property).2.1.1
      (by linarith [(huT i.property).2.1.2])).1)
    (fun i => (hballs i.val.1 (huT i.property).1 i.val.2 (huT i.property).2.1.1
      (by linarith [(huT i.property).2.1.2])).2.1.ne)
    (fun i => (huT i.property).2.2) hf
  rw [patchMaximal_superlevel]
  exact hmeasure.trans (by
    calc
      (ENNReal.ofReal C) ^ 3 * ∑' i : u, μ (ball i.val.1 i.val.2) ≤
          (ENNReal.ofReal C) ^ 3 * (eLpNorm f 1 (μ.restrict W) / ENNReal.ofReal t) := by gcongr
      _ = _ := by simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm])

/-- Lebesgue differentiation follows from the weak (1,1) maximal bound under the stated doubling-patch hypotheses (BB Theorem 7.27). -/
theorem lebesgue_differentiation_of_patch_hypotheses
    (μ : Measure X) (S W : Set X) (ρ C : ℝ) (hρ : 0 < ρ) (hC : 1 < C)
    (hinside : ∀ z ∈ S, ball z (6 * ρ) ⊆ W)
    (hballs : ∀ z ∈ S, ∀ s : ℝ, 0 < s → s ≤ 6 * ρ →
      0 < μ (ball z s) ∧ μ (ball z s) < ⊤ ∧
        μ (ball z s) ≤ ENNReal.ofReal C * μ (ball z (s / 2)))
    (hW : MeasurableSet W ∧ μ W < ⊤) (f : X → ℝ) (hf : IntegrableOn f W μ) :
    ∀ᵐ x ∂μ, x ∈ S →
      Filter.Tendsto (fun r : ℝ => ⨍ y in ball x r, |f y - f x| ∂μ) (𝓝[>] 0) (𝓝 0) ∧
      Filter.Tendsto (fun r : ℝ => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) ∧
      ‖f x‖ₑ ≤ patchMaximal μ S ρ f x := by
  exact lebesgue_differentiation_of_maximal_weak_type μ S W ρ C hρ hinside
    (fun x hx r hr hrρ => ⟨(hballs x hx r hr (by linarith)).1,
      (hballs x hx r hr (by linarith)).2.1⟩) hW
    (patchMaximal_weak_type μ S W ρ C hρ hC hinside hballs hW) f hf

end RothschildStein.H2

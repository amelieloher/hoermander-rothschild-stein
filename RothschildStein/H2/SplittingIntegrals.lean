-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SplittingVanishing

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Data D supplies the supported fractional piece on the doubled ball. -/
theorem LocalKernelData.supported_fractional (Q : LocalKernelData D d) :
    SupportedKernel D (ball Q.z Q.R) (ball Q.z (2 * Q.R)) Q.β Q.ν Q.A₁ Q.S₁ Q.R Q.K₁ := by
  refine ⟨isOpen_ball.measurableSet, ball_subset_ball (by linarith [Q.radius_pos]),
    Q.doubledBall_subset, Q.radius_pos, ?_, Q.fractional, ?_⟩
  · linarith [Q.radius_lt, D.κ_pos]
  · intro x hx y hy hr
    exact (Q.metric_support hx hy hr).2

/-- The inner cutoff gives an ae unit bound on every restriction. -/
theorem LocalKernelData.b_unit_bound (Q : LocalKernelData D d) (G : Set X) :
    ∀ᵐ y ∂D.μ.restrict G, |Q.b y| ≤ 1 := ae_of_all _ fun y => by
  rw [abs_of_nonneg (Q.cutoff_b.nonneg y)]
  exact Q.cutoff_b.le_one y

/-- Integrating the localized kernel over U is equivalent to integrating
its cutoff product over U₂, including arbitrary measurable truncation sets. -/
theorem LocalKernelData.localized_integral_eq (Q : LocalKernelData D d) {x : X}
    (hx : x ∈ ball Q.z Q.R) {S : Set X} (hS : MeasurableSet S) (K : X → X → ℝ) :
    (∫ y in ball Q.z Q.R ∩ S, localizedKernel (ball Q.z Q.R) Q.a Q.b K x y ∂D.μ) =
      Q.a x * ∫ y in ball Q.z (2 * Q.R) ∩ S, K x y * Q.b y ∂D.μ := by
  classical
  have hU : MeasurableSet (ball Q.z Q.R ∩ S) := isOpen_ball.measurableSet.inter hS
  have hU₂ : MeasurableSet (ball Q.z (2 * Q.R) ∩ S) := isOpen_ball.measurableSet.inter hS
  have hsub : ball Q.z Q.R ∩ S ⊆ ball Q.z (2 * Q.R) ∩ S :=
    inter_subset_inter_left S (ball_subset_ball (by linarith [Q.radius_pos]))
  have he : (∫ y in ball Q.z (2 * Q.R) ∩ S, K x y * Q.b y ∂D.μ) =
      ∫ y in ball Q.z Q.R ∩ S, K x y * Q.b y ∂D.μ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU₂ hsub (by
      intro y hy
      have hyU : y ∉ ball Q.z Q.R := fun h => hy.2 ⟨h, hy.1.2⟩
      rw [Q.cutoff_b.outside y hyU, mul_zero])
  rw [he, ← integral_const_mul]
  apply setIntegral_congr_fun hU
  intro y hy
  simp only [localizedKernel, hx, hy.1, and_self, ite_true]
  ring

/-- Explicit T(1) formula for Data D, BB Proposition 7.17, p. 307. -/
def LocalKernelData.oneLimit (Q : LocalKernelData D d) (x : X) : ℝ :=
  Q.a x * (regularizedIntegral D.μ (ball Q.z (2 * Q.R)) Q.K₀ Q.b x +
    fractionalIntegral D.μ (ball Q.z (2 * Q.R)) Q.K₁ Q.b x)

/-- Existence of the localized T(1) limit with its prescribed formula.
BB pp. 307–308; all input integrals use the doubled-ball domain. -/
theorem LocalKernelData.one_limit (Q : LocalKernelData D d) {x : X}
    (hx : x ∈ ball Q.z Q.R) :
    Tendsto (fun ε : ℝ => truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε (fun _ => 1) x)
      (𝓝[>] 0) (𝓝 (Q.oneLimit x)) := by
  have hm := Q.cutoff_b.lipschitz.continuous.measurable.aestronglyMeasurable
    (μ := D.μ.restrict (ball Q.z (2 * Q.R)))
  have hi₁ := (Q.supported_fractional.fractional_absolute Q.ν_pos hm (M := 1) (by norm_num)
    (Q.b_unit_bound _) hx).1
  have ht₁ := tendsto_truncated_of_integrable d isOpen_ball.measurableSet Q.doubledBall_subset
    (Q.doubledBall_subset (ball_subset_ball (by linarith [Q.radius_pos]) hx)) hi₁
  have ht := (Q.singular_b_limit hx).add ht₁
  have hmul := ht.const_mul (Q.a x)
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hm' : Measurable (d.d' x) := d.meas.comp (measurable_const.prodMk measurable_id)
  have hS : MeasurableSet {y | ε < d.d' x y} := measurableSet_lt measurable_const hm'
  have hi₀ := (Q.supported_singular.truncated_absolute d hε hm (M := 1) (by norm_num)
    (Q.b_unit_bound _) hx).1
  have hi₁' : IntegrableOn (fun y => Q.K₁ x y * Q.b y)
      (ball Q.z (2 * Q.R) ∩ {y | ε < d.d' x y}) D.μ := hi₁.mono_set inter_subset_left
  change Q.a x * (truncatedIntegral D.μ (ball Q.z (2 * Q.R)) d.d' Q.K₀ ε Q.b x +
    (∫ y in ball Q.z (2 * Q.R) ∩ {y | ε < d.d' x y}, Q.K₁ x y * Q.b y ∂D.μ)) = _
  unfold truncatedIntegral LocalKernelData.cutoffKernel
  simp only [mul_one]
  rw [Q.localized_integral_eq hx hS, ← integral_add hi₀ hi₁']
  congr 2
  funext y
  unfold LocalKernelData.sumKernel
  ring

end RothschildStein.H2

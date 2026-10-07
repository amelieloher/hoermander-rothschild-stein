-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.Operators
public import Hormander.A.Mollifier.Contraction

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap Metric
open scoped FourierTransform

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

theorem Eop_mollOp (δ : ℝ) (hδ : 0 < δ) (u : Tempered N) :
    Eop (mollOp N δ hδ) u = Hormander.A.Sδ N δ hδ u := by
  have := Eop_eq_ext (ExtOp.mollifier N δ hδ) (hct_mollOp δ hδ)
  rw [show (ExtOp.mollifier N δ hδ).op = mollOp N δ hδ from rfl] at this
  rw [this]
  exact ExtOp.ext_mollifier δ hδ u

/-- Mollification of a tempered distribution in `H^s` lies in every Sobolev space. -/
theorem Sδ_memSobolev_all {s : ℝ} (δ : ℝ) (hδ : 0 < δ) (T : Tempered N)
    (hT : TemperedDistribution.MemSobolev s 2 T) (t : ℝ) :
    TemperedDistribution.MemSobolev t 2 (Hormander.A.Sδ N δ hδ T) := by
  have hJ : (fun ξ : Carrier N => 𝓕 (Hormander.A.Jδ N δ hδ) ξ).HasTemperateGrowth :=
    (𝓕 (Hormander.A.Jδ N δ hδ)).hasTemperateGrowth
  have hb : (fun ξ : Carrier N => (((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    exact Function.HasTemperateGrowth.comp Complex.hasTemperateGrowth_ofReal
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Carrier N) ((t - s) / 2))
  have h1 : TemperedDistribution.MemSobolev s 2
      (TemperedDistribution.besselPotential (Carrier N) ℂ (t - s) (Hormander.A.Sδ N δ hδ T)) := by
    rw [Hormander.A.Sδ_eq_fourierMultiplier]
    unfold TemperedDistribution.besselPotential
    rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hJ hb]
    refine hT.fourierMultiplierCLM_of_bounded (hJ.mul hb) ?_
    let F : 𝓢(Carrier N, ℂ) := SchwartzMap.smulLeftCLM ℂ
      (fun ξ : Carrier N => (((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) : ℝ) : ℂ)) (𝓕 (Hormander.A.Jδ N δ hδ))
    refine ⟨‖F.toBoundedContinuousFunction‖, fun ξ => ?_⟩
    have hF : F ξ = (((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) : ℝ) : ℂ) * 𝓕 (Hormander.A.Jδ N δ hδ) ξ := by
      simp [F, SchwartzMap.smulLeftCLM_apply_apply hb]
    have : ((fun ξ : Carrier N => 𝓕 (Hormander.A.Jδ N δ hδ) ξ) *
        fun ξ : Carrier N => (((1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) : ℝ) : ℂ)) ξ = F ξ := by
      rw [hF]; simp [mul_comm]
    rw [this]
    exact F.toBoundedContinuousFunction.norm_coe_le_norm ξ
  have h2 := (TemperedDistribution.memSobolev_besselPotential_iff (E := Carrier N) (F := ℂ)
    (s := s) (r := t - s) (p := 2) (f := Hormander.A.Sδ N δ hδ T)).mp h1
  simpa using h2

/-- The mollifier kernel `J_δ` vanishes outside the ball of radius `δ / 2`. -/
theorem Jδ_eq_zero_of_gt {δ : ℝ} (hδ : 0 < δ) {z : Carrier N} (h : δ / 2 < ‖z‖) :
    Hormander.A.Jδ N δ hδ z = 0 := by
  rw [Hormander.A.Jδ_apply]
  have hz : Hormander.A.Jc N (δ⁻¹ • z) = 0 := by
    by_contra hne
    have hJ : Hormander.A.J N (δ⁻¹ • z) ≠ 0 := by
      intro h0; apply hne; simp [h0]
    have hmem : δ⁻¹ • z ∈ tsupport (Hormander.A.J N : Carrier N → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hJ)
    have hb := Hormander.A.J_tsupport_subset_closedBall_half hmem
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ] at hb
    have : δ⁻¹ * ‖z‖ ≤ 1 / 2 := hb
    have h3 : ‖z‖ ≤ δ / 2 := by
      have := mul_le_mul_of_nonneg_left this hδ.le
      rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at this
      linarith
    linarith
  rw [hz]; simp

/-- Locality of the mollifier: it only sees the `δ/2`-neighbourhood. -/
theorem SδSchwartz_apply_congr (δ : ℝ) (hδ : 0 < δ) (f g : TestFunction N) (x : Carrier N)
    (h : ∀ y, ‖x - y‖ ≤ δ / 2 → f y = g y) :
    Hormander.A.SδSchwartz N δ hδ f x = Hormander.A.SδSchwartz N δ hδ g x := by
  rw [Hormander.A.SδSchwartz_apply_eq_convolution, Hormander.A.SδSchwartz_apply_eq_convolution]
  unfold MeasureTheory.convolution
  simp only [ContinuousLinearMap.lsmul_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : ‖x - y‖ ≤ δ / 2
  · show f y • _ = g y • _
    rw [h y hy]
  · show f y • _ = g y • _
    rw [Jδ_eq_zero_of_gt hδ (not_le.mp hy)]; simp


/-- The mollification of a localized distribution is again localized. -/
theorem cutoffDistr_Sδ_fix (τ ψ : SchwartzMap (Carrier N) ℝ) (v : Tempered N)
    (hτ : cutoffDistr τ v = v) (δ : ℝ) (hδ : 0 < δ)
    (hψ : ∀ x ∈ tsupport (τ : Carrier N → ℝ), ∀ y, ‖x - y‖ ≤ δ / 2 → ψ y = 1) :
    cutoffDistr ψ (Hormander.A.Sδ N δ hδ v) = Hormander.A.Sδ N δ hδ v := by
  have hv : ∀ χ : TestFunction N, v χ = v (realMultiplierOperator τ χ) := by
    intro χ
    conv_lhs => rw [← hτ]
    rfl
  ext φ
  rw [cutoffDistr_apply_apply, Hormander.A.Sδ_apply, Hormander.A.Sδ_apply, hv, hv (Hormander.A.SδSchwartz N δ hδ φ)]
  congr 1
  ext x
  rw [realMultiplierOperator_apply, realMultiplierOperator_apply]
  by_cases hx : τ x = 0
  · simp [hx]
  · have hxs : x ∈ tsupport (τ : Carrier N → ℝ) := subset_tsupport _ hx
    congr 1
    apply SδSchwartz_apply_congr
    intro y hy
    rw [realMultiplierOperator_apply, hψ x hxs y hy]
    simp

/-- Existence of a uniform mollification radius. -/
theorem exists_mollifier_radius {τ ψ : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes τ ψ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x ∈ tsupport τ, ∀ y, ‖x - y‖ ≤ δ₀ → ψ y = 1 := by
  have hc : IsCompact (tsupport τ) := h.2.1
  have hsub : tsupport τ ⊆ interior {x | ψ x = 1} :=
    (Hormander.D.cutoffPrecedes_eventually_iff_interior τ ψ).mp h.2.2.2.2
  obtain ⟨δ₀, hδ₀, hth⟩ := hc.exists_cthickening_subset_open isOpen_interior hsub
  refine ⟨δ₀, hδ₀, fun x hx y hy => ?_⟩
  have : y ∈ Metric.cthickening δ₀ (tsupport τ) :=
    Metric.mem_cthickening_of_dist_le y x δ₀ _ hx (by rw [dist_comm, dist_eq_norm]; exact hy)
  exact (interior_subset (hth this) : y ∈ {x | ψ x = 1})

/-- Realization of a mollified localized `H^s` distribution as a Schwartz function. -/
theorem exists_testFunction_Sδ {s : ℝ} (τ ψ : SchwartzMap (Carrier N) ℝ)
    (hψc : HasCompactSupport (ψ : Carrier N → ℝ)) (v : Tempered N)
    (hv : TemperedDistribution.MemSobolev s 2 v) (hτ : cutoffDistr τ v = v)
    (δ : ℝ) (hδ : 0 < δ)
    (hψ : ∀ x ∈ tsupport (τ : Carrier N → ℝ), ∀ y, ‖x - y‖ ≤ δ / 2 → ψ y = 1) :
    ∃ g : TestFunction N, (g : Tempered N) = Hormander.A.Sδ N δ hδ v :=
  exists_schwartz_of_compactSupport _ (Sδ_memSobolev_all δ hδ v hv) ψ hψc
    (cutoffDistr_Sδ_fix τ ψ v hτ δ hδ hψ)

end Hormander.E

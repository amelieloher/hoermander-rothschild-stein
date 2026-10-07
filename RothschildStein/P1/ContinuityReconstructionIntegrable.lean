-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityReconstructionPV

/-!
# Reconstruction: absolutely convergent parts have a principal value

The far part of a degree-2 term is a regular kernel, so its truncated integrals converge to the
absolutely convergent integral (and so do those of positive-type kernels). This module records the
generic statement used to add the far part to the near part:

* `hasRhoPV_of_integrable`: if `η ↦ κ(ξ, η) f(η)` is integrable on `ℝ^{n+m}` and vanishes outside
  the chart domain `U`, then `HasRhoPV (ρ = ν ∘ Θ) κ f ξ (∫ κ(ξ, η) f(η) dη)` for `ξ ∈ U`
  (dominated convergence on the truncation sets `{ρ > ε}`, which increase to `{η ≠ ξ}`);
* `HasRhoPV.add_kernel`: the principal value is additive in the kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1

section Kernel

variable {N : ℕ} {ρ κ κ' : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} {f : (Fin N → ℝ) → ℝ}
  {ξ : Fin N → ℝ} {v w : ℝ}

/-- The principal value is additive in the kernel. -/
theorem HasRhoPV.add_kernel (h1 : HasRhoPV ρ κ f ξ v) (h2 : HasRhoPV ρ κ' f ξ w) :
    HasRhoPV ρ (fun ξ η => κ ξ η + κ' ξ η) f ξ (v + w) := by
  refine ⟨fun ε hε => ?_, ?_⟩
  · refine ((h1.1 ε hε).add (h2.1 ε hε)).congr (ae_of_all _ fun η => ?_)
    simp [add_mul]
  · refine (h1.2.add h2.2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    simp only [rhoTruncated, add_mul]
    exact (integral_add (h1.1 ε hε') (h2.1 ε hε')).symm

end Kernel

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- **Absolutely convergent integrals have a principal value.** For `ξ` in the chart domain,
a kernel slice `κ(ξ, ·)` and an input `f` with `κ(ξ, ·) f` integrable and vanishing outside `U`,
the `ρ`-truncations (`ρ = ν(Θ(η, ξ))`, `ν` a homogeneous gauge) are integrable and converge to
`∫ κ(ξ, η) f(η) dη` as `ε ↓ 0`. -/
theorem hasRhoPV_of_integrable {ν : (Fin (n + m) → ℝ) → ℝ} (hνg : C.G.IsHomogeneousGauge ν)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {f : (Fin (n + m) → ℝ) → ℝ}
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hout : ∀ η, η ∉ C.U → κ ξ η * f η = 0)
    (hint : Integrable (fun η => κ ξ η * f η) volume) :
    HasRhoPV (C.rhoGauge ν) κ f ξ (∫ η, κ ξ η * f η) := by
  classical
  have hν : Continuous ν := hνg.1
  obtain ⟨x, hxdef⟩ : ∃ x : C.Carrier, x = Carrier.mk ξ hξ := ⟨_, rfl⟩
  have hxξ : x.val = ξ := by rw [hxdef]; rfl
  obtain ⟨F, hF⟩ : ∃ F : (Fin (n + m) → ℝ) → ℝ, F = fun η => κ ξ η * f η := ⟨_, rfl⟩
  rw [← hF] at hint ⊢
  have hout' : ∀ η, η ∉ C.U → F η = 0 := by
    intro η hη
    rw [hF]
    exact hout η hη
  obtain ⟨G, hG⟩ : ∃ G : C.Carrier → ℝ, G = fun y => F y.val := ⟨_, rfl⟩
  have hGint : Integrable G volume := by
    rw [hG]
    exact (Carrier.integrable_iff_comp_val F hout').mp hint
  have hB : ∀ ε : ℝ, MeasurableSet {y : C.Carrier | ε < C.rho ν x y} := fun ε =>
    measurableSet_lt measurable_const
      ((C.continuous_rho hν).measurable.comp (measurable_const.prodMk measurable_id))
  have hUS : ∀ ε : ℝ, C.U ∩ {η | ε < C.rhoGauge ν ξ η} =
      Carrier.val '' {y : C.Carrier | ε < C.rho ν x y} := by
    intro ε
    ext η
    constructor
    · rintro ⟨hη, hεη⟩
      refine ⟨Carrier.mk η hη, ?_, rfl⟩
      show ε < C.rho ν x (Carrier.mk η hη)
      unfold rho
      rw [hxξ]
      exact hεη
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.val_mem, ?_⟩
      have hy' : ε < C.rho ν x y := hy
      unfold rho at hy'
      rw [hxξ] at hy'
      exact hy'
  have hξS : ∀ ε : ℝ, (∫ η in {η | ε < C.rhoGauge ν ξ η}, F η) =
      ∫ y in {y : C.Carrier | ε < C.rho ν x y}, G y ∂(volume : Measure C.Carrier) := fun ε => by
    rw [hG]
    exact (Carrier.setIntegral_eq_carrier_of_inter {η | ε < C.rhoGauge ν ξ η} F hout' (hB ε)
      (hUS ε)).1
  refine ⟨fun ε hε => ?_, ?_⟩
  · have h := (Carrier.setIntegral_eq_carrier_of_inter {η | ε < C.rhoGauge ν ξ η} F hout'
      (hB ε) (hUS ε)).2
    rw [hG] at hGint
    have h2 := h.mpr hGint.integrableOn
    rw [hF] at h2
    exact h2
  · have hlim : Tendsto (fun ε : ℝ => ∫ y, {y : C.Carrier | ε < C.rho ν x y}.indicator G y)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ y, G y)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖G y‖) ?_ ?_ hGint.norm ?_
      · exact Eventually.of_forall fun ε => hGint.aestronglyMeasurable.indicator (hB ε)
      · refine Eventually.of_forall fun ε => ae_of_all _ fun y => ?_
        by_cases hy : y ∈ {y : C.Carrier | ε < C.rho ν x y}
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy]; simp
      · have hne : ∀ᵐ y : C.Carrier ∂(volume : Measure C.Carrier), y ≠ x := by
          rw [ae_iff]
          have := Carrier.measure_singleton_eq_zero x
          simpa using this
        filter_upwards [hne] with y hy
        have hpos : 0 < C.rho ν x y := by
          unfold rho
          have hΘ : C.Θ y.val x.val ≠ 0 := by
            intro h
            exact hy ((Carrier.val_injective ((C.theta_eq_zero_iff y.val_mem x.val_mem).mp h)).symm)
          exact G2.gauge_pos hνg hΘ
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
        rw [indicator_of_mem (show y ∈ {y : C.Carrier | ε < C.rho ν x y} from hε.2)]
    rw [hG] at hlim
    have hint_eq : (∫ y : C.Carrier, F y.val) = ∫ η, F η :=
      (Carrier.integral_eq_comp_val F hout').symm
    rw [hint_eq] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hrt : rhoTruncated (C.rhoGauge ν) κ f ε ξ =
        ∫ η in {η | ε < C.rhoGauge ν ξ η}, F η := by
      rw [hF]; rfl
    rw [hrt, hξS ε, ← integral_indicator (hB ε), hG]

end LiftedChart

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledBasics
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace RothschildStein.G1

/-- A C¹ map on an open neighborhood of the curve image preserves
absolute continuity. Local Lipschitz constants are combined on that compact
image; no convexity of the domain is needed (BB Rem 1.40, p. 22). -/
theorem absolutelyContinuousOnInterval_comp_contDiffOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F} (hf : ContDiffOn ℝ 1 f Ω)
    {γ : ℝ → E} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hmap : MapsTo γ (uIcc a b) Ω) : AbsolutelyContinuousOnInterval (f ∘ γ) a b := by
  let K := γ '' uIcc a b
  have hcompact : IsCompact K := isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  have hlocal : LocallyLipschitzOn K f := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨L, s, hs, hL⟩ := (hf.contDiffAt (hΩ.mem_nhds (hmap hv))).exists_lipschitzOnWith
    exact ⟨L, s, mem_nhdsWithin_of_mem_nhds hs, hL⟩
  obtain ⟨L, hL⟩ := hlocal.exists_lipschitzOnWith_of_compact hcompact
  exact hL.comp_absolutelyContinuousOnInterval (fun v hv => mem_image_of_mem γ hv) hγ

/-- A C¹ field transport with weight-dependent dilation transports
actual controlled curves and their measurable controls. The drift factor is
scale² when its weight is two (BB Rem 1.40, p. 22). -/
theorem isControlledCurve_transport_scaled {m n k : ℕ} {Ω : Set (Fin n → ℝ)}
    {Ω' : Set (Fin k → ℝ)} (hΩ : IsOpen Ω) {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Z : Fin m → (Fin k → ℝ) → (Fin k → ℝ)} {F : (Fin n → ℝ) → (Fin k → ℝ)}
    (hF : ContDiffOn ℝ 1 F Ω) (hmap : MapsTo F Ω Ω') {scale : ℝ} (hscale : 0 < scale)
    (hfields : ∀ x ∈ Ω, ∀ i, fderiv ℝ F x (X i x) = scale ^ (w i : ℕ) • Z i (F x))
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ) :
    isControlledCurve Ω' w Z (scale * δ) (F ∘ γ) := by
  obtain ⟨hδ, hac, hrange, a, hmeas, ha⟩ := hγ
  refine ⟨mul_pos hscale hδ, absolutelyContinuousOnInterval_comp_contDiffOn hΩ hF hac
    (by simpa only [uIcc_of_le zero_le_one] using hrange),
    fun t ht => hmap (hrange ht), fun i t => scale ^ (w i : ℕ) * a i t,
    fun i => (hmeas i).const_mul _, ?_⟩
  filter_upwards [ha, ae_restrict_mem measurableSet_Icc] with t ht htime
  refine ⟨fun i => ?_, ?_⟩
  · rw [abs_mul, abs_of_pos (pow_pos hscale _), mul_pow]
    exact mul_le_mul_of_nonneg_left (ht.1 i) (pow_nonneg hscale.le _)
  · have hd := ((hF.contDiffAt (hΩ.mem_nhds (hrange htime))).differentiableAt
      one_ne_zero).hasFDerivAt.comp_hasDerivAt t ht.2
    simpa only [Function.comp_apply, map_sum, map_smul, hfields _ (hrange htime), smul_smul,
      mul_comm (a _ t)] using hd

/-- A C¹ field transport without dilation preserves the control
parameter (BB Rem 1.40, p. 22). -/
theorem isControlledCurve_transport {m n k : ℕ} {Ω : Set (Fin n → ℝ)}
    {Ω' : Set (Fin k → ℝ)} (hΩ : IsOpen Ω) {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Z : Fin m → (Fin k → ℝ) → (Fin k → ℝ)} {F : (Fin n → ℝ) → (Fin k → ℝ)}
    (hF : ContDiffOn ℝ 1 F Ω) (hmap : MapsTo F Ω Ω')
    (hfields : ∀ x ∈ Ω, ∀ i, fderiv ℝ F x (X i x) = Z i (F x))
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ) :
    isControlledCurve Ω' w Z δ (F ∘ γ) := by
  simpa only [one_mul] using isControlledCurve_transport_scaled hΩ hF hmap
    (scale := 1) zero_lt_one (by simpa only [one_pow, one_smul] using hfields) hγ

end RothschildStein.G1

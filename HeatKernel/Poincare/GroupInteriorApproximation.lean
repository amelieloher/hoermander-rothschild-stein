-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierSmooth
public import RothschildStein.G2.MollifierLpConvergence
public import RothschildStein.G2.MollifierExistence
public import RothschildStein.S.MollifierZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace HeatKernel
variable {N : ℕ} (G : RothschildStein.HomogeneousGroup N)

/-- Group convolution of zero extensions converges on every measurable subdomain. -/
theorem tendsto_groupRegularize_zeroExtension_local
    {ν : RothschildStein.G2.HomogeneousNorm G}
    (φ : RothschildStein.G2.GroupMollifier G ν)
    (Ω : Opens (Fin N → ℝ)) {D : Set (Fin N → ℝ)} (hD : MeasurableSet D)
    (hDΩ : D ⊆ Ω) {p : ℝ} (hp : 1 ≤ p)
    {f : (Fin N → ℝ) → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ)))) :
    Tendsto (fun ε : ℝ => eLpNorm
      (fun x => RothschildStein.G2.groupRegularize G φ
        ((Ω : Set (Fin N → ℝ)).indicator f) ε x - f x)
      (ENNReal.ofReal p) (volume.restrict D)) (𝓝[>] 0) (𝓝 0) := by
  have H := RothschildStein.G2.tendsto_groupRegularize_eLpNorm G φ hp
    ((RothschildStein.S.memLp_zeroExtension_iff Ω.isOpen.measurableSet f).mpr hf)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
  · exact Eventually.of_forall (fun _ => zero_le)
  · apply Eventually.of_forall
    intro ε
    have he : eLpNorm
        (fun x => RothschildStein.G2.groupRegularize G φ
          ((Ω : Set (Fin N → ℝ)).indicator f) ε x - f x)
        (ENNReal.ofReal p) (volume.restrict D) =
        eLpNorm (RothschildStein.G2.groupRegularize G φ
          ((Ω : Set (Fin N → ℝ)).indicator f) ε -
          (Ω : Set (Fin N → ℝ)).indicator f)
          (ENNReal.ofReal p) (volume.restrict D) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hD] with x hx
      simp only [Pi.sub_apply, indicator_of_mem (hDΩ hx)]
    rw [he]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- Smooth group convolutions approximate local Lp data along shrinking radii. -/
theorem exists_smooth_group_approximation
    (ν : RothschildStein.G2.HomogeneousNorm G)
    (Ω : Opens (Fin N → ℝ)) {p : ℝ} (hp : 1 ≤ p)
    {f : (Fin N → ℝ) → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ)))) :
    ∃ φ : RothschildStein.G2.GroupMollifier G ν,
      let u := fun n : ℕ => RothschildStein.G2.groupRegularize G φ
        ((Ω : Set (Fin N → ℝ)).indicator f) (1 / ((n : ℝ) + 1))
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n)) ∧
      ∀ D : Set (Fin N → ℝ), MeasurableSet D → D ⊆ Ω →
        Tendsto (fun n => eLpNorm (u n - f) (ENNReal.ofReal p)
          (volume.restrict D)) atTop (𝓝 0) := by
  obtain ⟨φ⟩ := RothschildStein.G2.nonempty_groupMollifier G ν
  refine ⟨φ, ?_, ?_⟩
  · intro n
    exact RothschildStein.G2.contDiff_groupRegularize G φ (by positivity)
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
      ((RothschildStein.S.memLp_zeroExtension_iff Ω.isOpen.measurableSet f).mpr hf)
  · intro D hD hDΩ
    exact (tendsto_groupRegularize_zeroExtension_local G φ Ω hD hDΩ hp hf).comp
      (tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall (fun n : ℕ => by
          change 0 < 1 / ((n : ℝ) + 1)
          positivity)⟩)

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierAllDimensions
public import RothschildStein.S.MollifierZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter TopologicalSpace
open scoped Topology ENNReal
namespace RothschildStein.S
variable {n : ℕ} {p : ℝ≥0∞}

/-- Zero-extended local Lp data converge on every
measurable subdomain, in every coordinate dimension
(BB Lemma 2.8 and Thm 2.9, pp. 72–73). -/
theorem tendsto_regularize_zeroExtension_local
    (Ω : Opens (Fin n → ℝ)) {U : Set (Fin n → ℝ)} (hU : MeasurableSet U)
    (hUΩ : U ⊆ Ω) (hp : 1 ≤ p) (ht : p ≠ ⊤)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p (volume.restrict (Ω : Set (Fin n → ℝ)))) :
    Tendsto (fun ε : ℝ => eLpNorm
      (fun x => euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε x-f x)
      p (volume.restrict U)) (𝓝[>] 0) (𝓝 0) := by
  have H := tendsto_euclideanRegularize_eLpNorm_all_dimensions p hp ht
    ((memLp_zeroExtension_iff Ω.isOpen.measurableSet f).mpr hf)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
  · exact Eventually.of_forall (fun _ => zero_le)
  · apply Eventually.of_forall
    intro ε
    have he : eLpNorm
        (fun x => euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε x-f x)
        p (volume.restrict U) =
        eLpNorm (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε-
          (Ω : Set (Fin n → ℝ)).indicator f) p (volume.restrict U) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      simp only [Pi.sub_apply,indicator_of_mem (hUΩ hx)]
    rw [he]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

end RothschildStein.S

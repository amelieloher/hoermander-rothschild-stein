-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderBounds
public import RothschildStein.S.MollifierZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ} {p : ℝ≥0∞}

/-- A locally measurable representative, bounded on a compact
support set within the domain, belongs to every Lp class. Values outside
the domain are irrelevant (BB p. 593; compact support). -/
theorem memLp_of_compact_local_support
    (Ω : Opens (Fin n → ℝ)) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {f : (Fin n → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hz : ∀ x ∈ (Ω : Set (Fin n → ℝ)) \ K,f x = 0)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hb : ∀ x ∈ K,‖f x‖ₑ ≤ C) :
    MemLp f p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  classical
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hfk := hf.mono_measure (Measure.restrict_mono_set volume hKΩ)
  have hk : MemLp f p (volume.restrict K) := MemLp.of_enorm_bound hfk hC (by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hb x hx)
  have hi : (Ω : Set (Fin n → ℝ)).indicator f = K.indicator f := by
    funext x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx,indicator_of_mem (hKΩ hx)]
    · by_cases ho : x ∈ (Ω : Set (Fin n → ℝ))
      · rw [indicator_of_mem ho,indicator_of_notMem hx,hz x ⟨ho,hx⟩]
      · rw [indicator_of_notMem ho,indicator_of_notMem hx]
  apply (memLp_zeroExtension_iff Ω.isOpen.measurableSet f).mp
  rw [hi]
  exact (memLp_zeroExtension_iff hK.measurableSet f).mpr hk

end RothschildStein.S

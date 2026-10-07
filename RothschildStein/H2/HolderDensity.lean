-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LipschitzDensity
public import RothschildStein.H2.HolderEstimates

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The approximation class belongs to every bounded Hölder space
on a bounded set, for exponents at most one (BB Remark 7.8, p. 298). -/
theorem BoundedLipschitz.boundedHolder {f : X → ℝ} (hf : BoundedLipschitz f)
    {δ : ℝ≥0} (hδ : δ ≤ 1) {U : Set X} (hU : Bornology.IsBounded U) :
    BoundedHolder δ U f := by
  obtain ⟨L, M, hl, hb⟩ := hf
  have hs : holderSup U f < ⊤ :=
    (holderSup_le_of_bound (fun x _ => hb x)).trans_lt ENNReal.ofReal_lt_top
  have hh : holderSemi δ U f < ⊤ :=
    (RothschildStein.H2.LipschitzWith.holderSemi_le_diam hl hU hδ).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)
  exact ENNReal.add_lt_top.mpr ⟨hs, hh⟩

/-- Density on a finite-measure open set, with a strict Lp error.
The functions are globally bounded Lipschitz; BB Remark 7.8, p. 298. -/
theorem exists_boundedLipschitz_on_open {μ : Measure X} {U : Set X}
    (_hU : IsOpen U) (hμU : μ U < ⊤) {p : ℝ≥0∞} (hp₁ : 1 ≤ p) (hp : p ≠ ⊤)
    {f : X → ℝ} (hf : MemLp f p (μ.restrict U)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, eLpNorm (f - g) p (μ.restrict U) < ENNReal.ofReal ε ∧ BoundedLipschitz g := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa using hμU⟩
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp₁)
  have hhalf : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨g, hg, hgl⟩ := exists_boundedLipschitz_eLpNorm_sub_le hp₀ hp hf hhalf.ne'
  refine ⟨g, hg.trans_lt ?_, hgl⟩
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

/-- Consequently bounded Hölder functions are dense on bounded open U.
BB Remark 7.8, p. 298. -/
theorem exists_boundedHolder_on_open {μ : Measure X} {U : Set X}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hμU : μ U < ⊤)
    {p : ℝ≥0∞} (hp₁ : 1 ≤ p) (hp : p ≠ ⊤) {δ : ℝ≥0} (hδ : δ ≤ 1)
    {f : X → ℝ} (hf : MemLp f p (μ.restrict U)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, eLpNorm (f - g) p (μ.restrict U) < ENNReal.ofReal ε ∧ BoundedHolder δ U g := by
  obtain ⟨g, hg, hgl⟩ := exists_boundedLipschitz_on_open hU hμU hp₁ hp hf hε
  exact ⟨g, hg, hgl.boundedHolder hδ hUb⟩

end RothschildStein.H2

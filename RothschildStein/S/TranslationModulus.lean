-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.LpTranslations
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RothschildStein.S
variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The supremum of Lp translation increments on a closed ball
(BB Lemma 2.8, p. 72; translation). -/
def translationModulus (f : Lp ℝ p (volume : Measure (Fin n → ℝ))) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ w : {w : Fin n → ℝ // ‖w‖ ≤ ε}, eLpNorm (fun x => f (x+w.val)-f x) p volume

omit [Fact (1 ≤ p)] in
/-- The translation modulus bounds each increment in the ball
(BB Lemma 2.8, p. 72). -/
theorem translation_increment_le_modulus
    (f : Lp ℝ p (volume : Measure (Fin n → ℝ))) (ε : ℝ)
    (w : Fin n → ℝ) (hw : ‖w‖ ≤ ε) :
    eLpNorm (fun x => f (x+w)-f x) p volume ≤ translationModulus f ε :=
  le_iSup (fun w : {w : Fin n → ℝ // ‖w‖ ≤ ε} =>
    eLpNorm (fun x => f (x+w.val)-f x) p volume) ⟨w,hw⟩

/-- The supremum over all displacements of size at most ε tends
to zero for finite p (BB Lemma 2.8, p. 72; translation). -/
theorem tendsto_translationModulus (hp : p ≠ ⊤)
    (f : Lp ℝ p (volume : Measure (Fin n → ℝ))) :
    Tendsto (translationModulus f) (𝓝[>] 0) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  have hh := ENNReal.tendsto_nhds_zero.mp (tendsto_translation_increment hp f) η hη
  obtain ⟨δ,hδ,hbound⟩ := Metric.mem_nhds_iff.mp hh
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (half_pos hδ))] with ε hε
  apply iSup_le
  intro w
  apply hbound
  change dist w.val 0 < δ
  rw [dist_zero_right]
  exact lt_of_le_of_lt w.property (hε.trans (half_lt_self hδ))

end RothschildStein.S

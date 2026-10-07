-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- The Lᵖ functions which also belong to L², used in interpolation. -/
def lpL2Intersection (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (Lp ℝ p μ) where
  carrier := {v | MemLp v 2 μ}
  zero_mem' := by
    exact (memLp_congr_ae (Lp.coeFn_zero ℝ p μ)).mpr MemLp.zero
  add_mem' := by
    intro v w hv hw
    exact (memLp_congr_ae (Lp.coeFn_add v w)).mpr (hv.add hw)
  smul_mem' := by
    intro c v hv
    exact (memLp_congr_ae (Lp.coeFn_smul c v)).mpr (hv.const_smul c)

/-- Lᵖ ∩ L² is dense in Lᵖ on a finite-measure space,
using the simple-function approximation (BB p. 326). -/
theorem lpL2Intersection_dense (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    DenseRange (lpL2Intersection μ p).subtype := by
  have hsubset : Set.range ((↑) : Lp.simpleFunc ℝ p μ → Lp ℝ p μ) ⊆
      Set.range (lpL2Intersection μ p).subtype := by
    rintro v ⟨s, rfl⟩
    have h2 : MemLp (fun x => (s : Lp ℝ p μ) x) 2 μ :=
      (memLp_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun s)).mp
        ((Lp.simpleFunc.toSimpleFunc s).memLp_of_isFiniteMeasure 2 μ)
    exact ⟨⟨s, h2⟩, rfl⟩
  exact (Lp.simpleFunc.denseRange hp).mono hsubset

/-- Convert the intersection to its L² class. -/
def lpL2ToL2 (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    lpL2Intersection μ p →ₗ[ℝ] Lp ℝ 2 μ where
  toFun v := v.property.toLp (fun x => (v : Lp ℝ p μ) x)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(v + w).property.coeFn_toLp, v.property.coeFn_toLp, w.property.coeFn_toLp,
      Lp.coeFn_add (v.property.toLp _) (w.property.toLp _),
      Lp.coeFn_add (v : Lp ℝ p μ) (w : Lp ℝ p μ)] with x hx hv hw ha hb
    rw [hx, ha]
    change ((v : Lp ℝ p μ) + (w : Lp ℝ p μ)) x = _
    rw [hb]
    simp only [Pi.add_apply]
    rw [hv, hw]
  map_smul' c v := by
    change (c • v).property.toLp _ = c • v.property.toLp _
    apply Lp.ext
    filter_upwards [(c • v).property.coeFn_toLp, v.property.coeFn_toLp,
      Lp.coeFn_smul c (v.property.toLp _), Lp.coeFn_smul c (v : Lp ℝ p μ)] with x hx hv ha hb
    rw [hx, ha]
    change (c • (v : Lp ℝ p μ)) x = _
    rw [hb]
    simp only [Pi.smul_apply]
    rw [hv]

end RothschildStein.H2

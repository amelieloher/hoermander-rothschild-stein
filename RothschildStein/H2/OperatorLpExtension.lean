-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LpIntersection

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- The operator on the dense Lᵖ/L² intersection. -/
def intersectionOperator (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ v : Lp ℝ 2 μ, MemLp v p μ → MemLp (fun x => (T v) x) p μ) :
    lpL2Intersection μ p →ₗ[ℝ] Lp ℝ p μ := by
  have hp : ∀ v : lpL2Intersection μ p, MemLp (lpL2ToL2 μ p v) p μ := fun v =>
    (memLp_congr_ae v.property.coeFn_toLp).mpr (Lp.memLp (v : Lp ℝ p μ))
  let out : lpL2Intersection μ p → Lp ℝ p μ := fun v =>
    (hT (lpL2ToL2 μ p v) (hp v)).toLp (fun x => (T (lpL2ToL2 μ p v)) x)
  refine { toFun := out, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    apply Lp.ext
    have hv := (hT (lpL2ToL2 μ p v) (hp v)).coeFn_toLp
    have hw := (hT (lpL2ToL2 μ p w) (hp w)).coeFn_toLp
    have ha := (hT (lpL2ToL2 μ p (v + w)) (hp (v + w))).coeFn_toLp
    filter_upwards [ha, hv, hw, Lp.coeFn_add (out v) (out w),
      Lp.coeFn_add (T (lpL2ToL2 μ p v)) (T (lpL2ToL2 μ p w))] with x hax hvx hwx hs ht
    change out (v + w) x = (out v + out w) x
    rw [hax, hs]
    simp only [Pi.add_apply]
    rw [hvx, hwx, map_add, T.map_add, ht]
    rfl
  · intro c v
    change out (c • v) = c • out v
    apply Lp.ext
    have hv := (hT (lpL2ToL2 μ p v) (hp v)).coeFn_toLp
    have ha := (hT (lpL2ToL2 μ p (c • v)) (hp (c • v))).coeFn_toLp
    filter_upwards [ha, hv, Lp.coeFn_smul c (out v),
      Lp.coeFn_smul c (T (lpL2ToL2 μ p v))] with x hax hvx hs ht
    rw [hax, hs]
    simp only [Pi.smul_apply]
    rw [hvx, map_smul, T.map_smul, ht]
    rfl

/-- Extend a proved Lᵖ bound on the L² operator to the full
Lᵖ space; equality is retained on Lᵖ ∩ L² (BB p. 326). -/
theorem operator_lp_extension_of_bound (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v : Lp ℝ 2 μ, MemLp v p μ →
      MemLp (fun x => (T v) x) p μ ∧ eLpNorm (fun x => (T v) x) p μ ≤ ENNReal.ofReal C * eLpNorm v p μ) :
    ∃ Tp : Lp ℝ p μ →L[ℝ] Lp ℝ p μ, ‖Tp‖ ≤ C ∧
      (∀ v : lpL2Intersection μ p,
        (fun x => (Tp (v : Lp ℝ p μ)) x) =ᵐ[μ] fun x => (T (lpL2ToL2 μ p v)) x) := by
  let hT := fun v hv => (hbound v hv).1
  let F := intersectionOperator μ p T hT
  have hd := lpL2Intersection_dense μ p hp
  have hnorm : ∀ v : lpL2Intersection μ p, ‖F v‖ ≤ C * ‖(v : Lp ℝ p μ)‖ := by
    intro v
    have hvp : MemLp (lpL2ToL2 μ p v) p μ :=
      (memLp_congr_ae v.property.coeFn_toLp).mpr (Lp.memLp (v : Lp ℝ p μ))
    have he : eLpNorm (lpL2ToL2 μ p v) p μ = eLpNorm (v : Lp ℝ p μ) p μ :=
      eLpNorm_congr_ae v.property.coeFn_toLp
    have hb := (hbound (lpL2ToL2 μ p v) hvp).2
    rw [he] at hb
    change ‖(hT (lpL2ToL2 μ p v) hvp).toLp _‖ ≤ _
    rw [Lp.norm_toLp, Lp.norm_def]
    have ht : ENNReal.ofReal C * eLpNorm (v : Lp ℝ p μ) p μ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ht hb
  refine ⟨F.extendOfNorm (lpL2Intersection μ p).subtype,
    LinearMap.opNorm_extendOfNorm_le hd hC hnorm, ?_⟩
  intro v
  have heq : F.extendOfNorm (lpL2Intersection μ p).subtype (v : Lp ℝ p μ) = F v :=
    LinearMap.extendOfNorm_eq hd ⟨C, hnorm⟩ v
  rw [heq]
  exact (hT (lpL2ToL2 μ p v)
    ((memLp_congr_ae v.property.coeFn_toLp).mpr (Lp.memLp (v : Lp ℝ p μ)))).coeFn_toLp

end RothschildStein.H2

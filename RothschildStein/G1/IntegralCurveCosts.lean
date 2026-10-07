-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.GeneratorCosts
public import RothschildStein.G1.LocalFlows

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- A defined generator integral curve rescales to a C¹ arc on [0,1],
with its actual constant-speed derivative and range preserved. Both signs of
time are included (BB Rem 1.34, pp. 18–19; Rem 1.40, p. 22). -/
theorem integralCurve_generatorArc {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : (Fin n → ℝ) → (Fin n → ℝ)} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω)
    {α : ℝ → (Fin n → ℝ)} {a b t : ℝ} (hzero : (0 : ℝ) ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hα : ∀ v ∈ Ioo a b, HasDerivAt α (Z (α v)) v ∧ α v ∈ Ω) :
    ContDiffOn ℝ 1 (fun v => α (t * v)) (Icc 0 1) ∧
      MapsTo (fun v => α (t * v)) (Icc 0 1) Ω ∧
      ∀ v ∈ Icc 0 1, HasDerivAt (fun w => α (t * w)) (t • Z (α (t * v))) v := by
  have hsub : uIcc 0 t ⊆ Ioo a b := ordConnected_Ioo.uIcc_subset hzero ht
  have hmap : ∀ v ∈ Icc (0 : ℝ) 1, t * v ∈ Ioo a b := by
    intro v hv
    apply hsub
    rcases le_total 0 t with ht0 | ht0
    · rw [uIcc_of_le ht0]; constructor <;> nlinarith [hv.1, hv.2]
    · rw [uIcc_of_ge ht0]; constructor <;> nlinarith [hv.1, hv.2]
  have hs := integralCurve_contDiffOn Z hZ α (fun v hv => (hα v hv).1) (fun v hv => (hα v hv).2)
  refine ⟨(hs.of_le (by simp)).comp (contDiffOn_const.mul contDiffOn_id) hmap,
    fun v hv => (hα _ (hmap v hv)).2, ?_⟩
  intro v hv
  have hd := (hα _ (hmap v hv)).1.scomp v ((hasDerivAt_id v).const_mul t)
  simpa only [Function.comp_def, id_eq, mul_one] using hd

end RothschildStein.G1

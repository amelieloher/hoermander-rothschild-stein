-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.S.Transposes
public import RothschildStein.G1.BracketAlgebra
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3
local instance smoothFunctionOperatorsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Smooth scalar functions on the open coefficient domain, retaining
an ambient representative (BB Lemma 9.22, pp. 413–414). -/
def smoothOnFunctions {N : ℕ} (Ω : Opens (Fin N → ℝ)) :
    Submodule ℝ ((Fin N → ℝ) → ℝ) where
  carrier := {f | ContDiffOn ℝ (⊤ : ℕ∞) f Ω}
  zero_mem' := contDiffOn_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _f hf := hf.const_smul c

/-- The field operator on smooth representatives; outside the open
coefficient domain its value is set to zero to preserve linearity
(BB Lemma 9.22, pp. 413–414). -/
def smoothFieldOperator {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) :
    Module.End ℝ (smoothOnFunctions Ω) where
  toFun f := ⟨fun x => if x ∈ Ω then fieldDerivative V f.val x else 0,
    (S.contDiffOn_fieldDerivative Ω V f.val hV f.property).congr
      (fun x hx => ite_eq_left hx)⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ Ω
    · simp only [hx, ite_true, Submodule.coe_add, Pi.add_apply, fieldDerivative]
      rw [fderiv_add ((f.property.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
        ((g.property.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)),
        add_apply]
    · simp [hx]
  map_smul' c f := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ Ω
    · simp only [hx, ite_true, Submodule.coe_smul, Pi.smul_apply, fieldDerivative]
      rw [fderiv_const_smul ((f.property.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)) c,
        smul_apply, RingHom.id_apply]
    · simp [hx]

/-- The bundled linear operator acts as the actual field derivative
at every point of the coefficient domain (BB Lemma 9.22, pp. 413–414). -/
theorem smoothFieldOperator_apply {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) (f : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (smoothFieldOperator Ω V hV f).val x = fieldDerivative V f.val x := by
  change (if x ∈ Ω then fieldDerivative V f.val x else 0) = _
  exact ite_eq_left hx
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PrimitiveFlowFromLieFamily
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- The retained family gives genuine primitive ODE arcs by one fixed
coefficient/time rescaling. -/
theorem primitiveFlowFromLieFamily_ode {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ : ℝ} (hκ : 0 < κ)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),t) ∈ Ω ∧
          HasDerivAt (fun v => Φ ((D.basis.equivFun z,x),v))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),t))) t)
    (i : Fin a) (hi : (p i : ℕ) ≤ s)
    (hcoeff : D.basis.equivFun (κ • (wordLieElement [i] : formalSpan a s p)) ∈ ball 0 σ) :
    ∀ x ∈ Ω₀, primitiveFlowFromLieFamily D Φ κ i (x,0) = x ∧
      ∀ t ∈ Ioo (-κ) κ, primitiveFlowFromLieFamily D Φ κ i (x,t) ∈ Ω ∧
        HasDerivAt (fun v => primitiveFlowFromLieFamily D Φ κ i (x,v))
          (X i (primitiveFlowFromLieFamily D Φ κ i (x,t))) t := by
  intro x hx
  let f : formalSpan a s p := wordLieElement [i]
  have ha := hODE (κ • f) hcoeff x hx
  refine ⟨?_,?_⟩
  · simpa only [primitiveFlowFromLieFamily,zero_div] using ha.1
  · intro t ht
    have htt : t/κ ∈ Ioo (-2 : ℝ) 2 := by
      apply abs_lt.mp
      rw [abs_div,abs_of_pos hκ]
      exact ((div_lt_one hκ).mpr (abs_lt.mpr ht)).trans (by norm_num)
    have hy := (ha.2 _ htt).1
    refine ⟨hy,?_⟩
    have hfield : finiteLieField D X (κ • f) (Φ ((D.basis.equivFun (κ • f),x),t/κ)) =
        κ • X i (Φ ((D.basis.equivFun (κ • f),x),t/κ)) := by
      have he := congrArg (fun Z : (Fin N → ℝ) → (Fin N → ℝ) => Z (Φ ((D.basis.equivFun (κ • f),x),t/κ)))
        ((finiteLieFieldLinear D X).map_smul κ f)
      have hw : finiteLieField D X f (Φ ((D.basis.equivFun (κ • f),x),t/κ)) =
          X i (Φ ((D.basis.equivFun (κ • f),x),t/κ)) := by
        simpa only [wordBracket] using finiteLieField_word D Ω X hX [i] (by simp)
          (by simpa only [wordWeight,List.map_singleton,List.sum_singleton] using hi) hy
      have he' : finiteLieField D X (κ • f) (Φ ((D.basis.equivFun (κ • f),x),t/κ)) =
          κ • finiteLieField D X f (Φ ((D.basis.equivFun (κ • f),x),t/κ)) := by
        simpa only [finiteLieFieldLinear_apply,Pi.smul_apply] using he
      exact he'.trans (congrArg (fun z : Fin N → ℝ => κ • z) hw)
    have hinner : HasDerivAt (fun v : ℝ => v/κ) (1/κ) t := by
      simpa only [id_eq] using (hasDerivAt_id t).div_const κ
    have hd := ((ha.2 _ htt).2).scomp t hinner
    have hc : (1/κ)*κ = 1 := by field_simp
    simpa only [Function.comp_def,primitiveFlowFromLieFamily,hfield,smul_smul,hc,one_smul] using hd
end RothschildStein.G3

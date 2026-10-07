-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderFaithful
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Concrete Hölder functions, normalized to zero outside U.
The normalization removes irrelevant values outside the integration patch. -/
def holderFunctions (δ : ℝ≥0) (U : Set X) : Submodule ℝ (X → ℝ) where
  carrier := {f | BoundedHolder δ U f ∧ ∀ x, x ∉ U → f x = 0}
  zero_mem' := ⟨boundedHolder_zero δ U, fun _ _ => rfl⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  smul_mem' := fun c _ hf => ⟨hf.1.smul c, fun x hx => by simp [hf.2 x hx]⟩

/-- Normalize a Hölder representative without changing it on U. -/
def holderNormalize {δ : ℝ≥0} {U : Set X} {f : X → ℝ} (hf : BoundedHolder δ U f) :
    holderFunctions δ U :=
  ⟨U.indicator f, by
    constructor
    · unfold BoundedHolder
      rw [boundedHolderNorm_congr (fun x hx => indicator_of_mem hx f)]
      exact hf
    · exact fun x hx => indicator_of_notMem hx f⟩

/-- The full Hölder norm is a genuine finite seminorm on this module. -/
def holderFunctionSeminorm (δ : ℝ≥0) (U : Set X) : Seminorm ℝ (holderFunctions δ U) :=
  Seminorm.of (fun f => (boundedHolderNorm δ U f).toReal)
    (fun f g => by
      have hf := f.property.1
      have hg := g.property.1
      have he := ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨hf, hg⟩).ne
        (boundedHolderNorm_add_le (δ := δ) (G := U) (f := f) (g := g))
      have hfun : ((f + g : holderFunctions δ U) : X → ℝ) =
          (fun x => (f : X → ℝ) x + (g : X → ℝ) x) := by funext x; rfl
      rw [hfun]
      simpa only [ENNReal.toReal_add hf.ne hg.ne] using he)
    (fun c f => by
      change (boundedHolderNorm δ U (c • (f : X → ℝ))).toReal = _
      rw [boundedHolderNorm_smul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg c), Real.norm_eq_abs]
      )

/-- The linear embedding of concrete Hölder functions into L²(U). -/
def holderL2 (δ : ℝ≥0) (U : Set X) (μ : Measure X)
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤) :
    holderFunctions δ U →ₗ[ℝ] Lp ℝ 2 (μ.restrict U) where
  toFun f := (f.property.1.memLp_two hδ hU hμ).toLp f
  map_add' _f _g := MemLp.toLp_add _ _
  map_smul' c _f := MemLp.toLp_const_smul c _

/-- Positivity of local balls makes the L² embedding injective. -/
theorem holderL2_injective (D : LocDoubling X) {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : IsOpen U) (hU₁ : U ⊆ D.Ω₁) (hμ : D.μ U < ⊤) :
    Function.Injective (holderL2 δ U D.μ hδ hU.measurableSet hμ) := by
  intro f g hfg
  have hf := f.property.1.memLp_two hδ hU.measurableSet hμ
  have hg := g.property.1.memLp_two hδ hU.measurableSet hμ
  change hf.toLp (f : X → ℝ) = hg.toLp (g : X → ℝ) at hfg
  have he : (f : X → ℝ) =ᵐ[D.μ.restrict U] g :=
    (MemLp.toLp_eq_toLp_iff hf hg).mp hfg
  have hp := D.eqOn_of_ae_eq hU hU₁ (f.property.1.continuousOn hδ)
    (g.property.1.continuousOn hδ) he
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ U
  · exact hp hx
  · rw [f.property.2 x hx, g.property.2 x hx]

end RothschildStein.H2

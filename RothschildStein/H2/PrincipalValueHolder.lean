-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.RegularizedHolderNorm
public import RothschildStein.H2.HolderOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The principal-value Hölder bound, with the precise diameter
factor for the T(1) exponent comparison. BB (7.12), p. 304. -/
theorem SupportedKernel.principalValue_holder_norm_le {D : LocDoubling X} {E G : Set X}
    {β A S R C_K : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    (d : TruncDist D) (hCan : ShellCancellation D.μ E G d.d' K C_K)
    {δ γ : ℝ≥0} (hδ : 0 < δ) (hδβ : (δ : ℝ) < β) (hδγ : δ ≤ γ)
    {f h : X → ℝ} (hf : BoundedHolder δ G f) (hh : BoundedHolder γ E h) :
    boundedHolderNorm δ E (pvFormula D.μ G K h f) ≤
      (ENNReal.ofReal (regularizedHolderConstant β δ D.C_D d.θ₁ d.θ₂ * (A + S + C_K) +
        volumeIntegralConstant D.C_D δ * A * R ^ (δ : ℝ)) +
        ENNReal.ofReal (max 1 (diam E ^ ((γ : ℝ) - δ))) * boundedHolderNorm γ E h) *
          boundedHolderNorm δ G f := by
  have hEb : Bornology.IsBounded E := D.cpt.isBounded.subset (by
    intro x hx
    exact subset_closure (D.sub₁₂ (hK.sub_G (hK.sub_EG hx))))
  have hhδ := boundedHolderNorm_le_diam hEb hδγ hh
  have hfE := boundedHolderNorm_restrict (δ := δ) (f := f) hK.sub_EG
  have hr := hK.regularized_holder_norm_le d hCan hδ hδβ hf
  have hHδ : BoundedHolder δ E h := hhδ.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh)
  have hFE : BoundedHolder δ E f := hfE.trans_lt hf
  have hp := boundedHolderNorm_mul_le hHδ hFE
  have hb := boundedHolderNorm_add_le (δ := δ) (G := E)
    (f := regularizedIntegral D.μ G K f) (g := fun x => h x * f x)
  change boundedHolderNorm δ E (fun x => regularizedIntegral D.μ G K f x + h x * f x) ≤ _
  calc
    _ ≤ boundedHolderNorm δ E (regularizedIntegral D.μ G K f) + boundedHolderNorm δ E (fun x => h x * f x) := hb
    _ ≤ ENNReal.ofReal (regularizedHolderConstant β δ D.C_D d.θ₁ d.θ₂ * (A + S + C_K) +
        volumeIntegralConstant D.C_D δ * A * R ^ (δ : ℝ)) * boundedHolderNorm δ G f +
        (ENNReal.ofReal (max 1 (diam E ^ ((γ : ℝ) - δ))) * boundedHolderNorm γ E h) * boundedHolderNorm δ G f := by
      apply add_le_add
      · apply hr.trans
        apply mul_le_mul_right
        exact le_add_left le_rfl
      · exact hp.trans (mul_le_mul hhδ hfE (by exact bot_le) (by exact bot_le))
    _ = _ := (add_mul _ _ _).symm

end RothschildStein.H2

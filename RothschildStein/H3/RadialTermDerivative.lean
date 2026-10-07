-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialGaugeProducts
public import RothschildStein.H3.RadialFieldChain
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
open scoped Topology

/-- One summand of the finite radial chain-rule expansion. -/
def radialTermValue {n m : ℕ} (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (ν : (Fin n → ℝ) → ℝ) (F : ℝ → ℝ) (t : ℕ × List (List (Fin m)))
    (x : Fin n → ℝ) : ℝ := iteratedDeriv t.1 F (ν x) * radialGaugeProduct X ν t.2 x

/-- Each finite radial expansion summand is differentiable off the origin. -/
theorem radialTermValue_differentiableAt {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {ν : (Fin n → ℝ) → ℝ}
    (hν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℕ × List (List (Fin m)))
    {x : Fin n → ℝ} (hx : x ≠ 0) : DifferentiableAt ℝ (radialTermValue X ν F t) x := by
  have hdν := (hν.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  exact (((hF.of_le (by simp)).differentiable_iteratedDeriv' t.1).differentiableAt.comp x hdν).mul
    (((radialGaugeProduct_contDiffOn X hX hν t.2).contDiffAt
      (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp))

/-- The chain rule differentiates the profile once or one gauge
 factor once; the finite term list keeps all repetitions. -/
theorem fieldDerivative_radialTermValue {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {ν : (Fin n → ℝ) → ℝ}
    (hν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin m) (t : ℕ × List (List (Fin m)))
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    fieldDerivative (X i) (radialTermValue X ν F t) x =
      radialTermValue X ν F (t.1+1,[i]::t.2) x +
      ((radialFactorDerivatives i t.2).map (fun Ks => radialTermValue X ν F (t.1,Ks) x)).sum := by
  have hdν := (hν.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  have hdF := (hF.of_le (by simp)).differentiable_iteratedDeriv' t.1
  have hdP := ((radialGaugeProduct_contDiffOn X hX hν t.2).contDiffAt
    (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  change fieldDerivative (X i) (fun y => iteratedDeriv t.1 F (ν y) * radialGaugeProduct X ν t.2 y) x = _
  have hdc : DifferentiableAt ℝ (fun y => iteratedDeriv t.1 F (ν y)) x := by
    simpa only [Function.comp_def] using hdF.differentiableAt.comp x hdν
  rw [RothschildStein.S.fieldDerivative_mul (X i)
    (fun y => iteratedDeriv t.1 F (ν y)) _ x hdc hdP]
  have hc : fieldDerivative (X i) (fun y => iteratedDeriv t.1 F (ν y)) x =
      iteratedDeriv (t.1+1) F (ν x) * fieldDerivative (X i) ν x := by
    simpa only [Function.comp_def,iteratedDeriv_succ] using
      fieldDerivative_scalar_comp (X i) hdF.differentiableAt hdν
  rw [hc,fieldDerivative_radialGaugeProduct X hX hν i t.2 hx]
  simp only [radialTermValue,radialGaugeProduct,wordDerivative,List.sum_map_mul_left,mul_assoc]

end RothschildStein.H3

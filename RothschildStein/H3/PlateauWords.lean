-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FirstCutoffBound
public import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Filter
open scoped Topology
variable {N m : ℕ}

/-- Arbitrary classical words depend only on the local function germ. -/
theorem wordDerivative_germ
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin m))
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (he : f =ᶠ[𝓝 x] g) :
    wordDerivative X I f =ᶠ[𝓝 x] wordDerivative X I g := by
  induction I with
  | nil => exact he
  | cons i I ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (X i y)) hy

/-- Every nonempty word annihilates constants. -/
theorem wordDerivative_const
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin m)) (c : ℝ) :
    wordDerivative X I (fun _ => c) = (fun _ => if I = [] then c else 0) := by
  induction I with
  | nil => simp only [wordDerivative, ite_true]
  | cons i I ih =>
    funext x
    change fieldDerivative (X i) (wordDerivative X I (fun _ => c)) x = _
    rw [ih]
    simp only [fieldDerivative, fderiv_const_apply, zero_apply, List.cons_ne_nil, ite_false]

/-- All nonempty cutoff derivative words vanish on the inner plateau,
including the origin. No smoothness of the gauge at zero is required. -/
theorem radialProfile_wordDerivative_zero_below (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin m)) (hI : I ≠ [])
    {t s : ℝ} (hts : t < s) {x : Fin N → ℝ} (hx : ν x < t) :
    wordDerivative X I (quasiballProfile t s ∘ ν) x = 0 := by
  have he : (quasiballProfile t s ∘ ν) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [(isOpen_lt ν.gauge.1 continuous_const).mem_nhds hx] with y hy
    exact quasiballProfile_one hts hy.le
  have hw := (wordDerivative_germ X I he).self_of_nhds
  simpa only [wordDerivative_const, ite_eq_right hI] using hw

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.S
variable {n q : ℕ}

/-- A continuous weak word derivative vanishes
pointwise off the closed local support of its input. This uses no
Hölder norm or distance geometry
(BB p. 73 and Thm 2.20, p. 86; continuous locality adapter). -/
theorem continuous_weakWord_zero_off_support
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q))
    {f g : (Fin n → ℝ) → ℝ} (hg : hasWeakWordDeriv X Ω I f g)
    (hc : ContinuousOn g (Ω : Set (Fin n → ℝ)))
    {K : Set (Fin n → ℝ)} (hK : IsClosed K)
    (hz : ∀ x ∈ (Ω : Set (Fin n → ℝ)) \ K,f x = 0) :
    ∀ x ∈ (Ω : Set (Fin n → ℝ)) \ K,g x = 0 := by
  let V : Opens (Fin n → ℝ) := ⟨(Ω : Set (Fin n → ℝ)) \ K,Ω.isOpen.sdiff hK⟩
  have hs : (V : Set (Fin n → ℝ)) ⊆ Ω := fun _ hx => hx.1
  have ha : f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    exact hz x hx
  exact Measure.eqOn_open_of_ae_eq (hasWeakWordDeriv_locality X Ω V hs hg ha)
    V.isOpen (hc.mono hs) continuousOn_const

end RothschildStein.S

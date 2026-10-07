-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderSubsetContinuity
public import RothschildStein.S.WeakHolderSpaces
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- Weak Hölder data have a continuous pointwise empty
representative on every open subdomain (BB Def 2.13, p. 81). -/
theorem memWeakHolderX_continuousOn
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (k : ℕ) {α : ℝ} (hα : 0 < α)
    {f : (Fin n → ℝ) → ℝ} (hf : memWeakHolderX w X G.d U k α f) :
    ContinuousOn f (U : Set (Fin n → ℝ)) :=
  continuousOn_of_holderENorm_lt_top_subset Ω G hU hα hf.1

/-- Continuous weak Hölder word representatives are unique
pointwise on the open domain (BB Def 2.13, p. 81). -/
theorem eqOn_of_weakHolder_representatives
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q))
    {α : ℝ} (hα : 0 < α) {f g h : (Fin n → ℝ) → ℝ}
    (hg : hasWeakWordDeriv X U I f g) (hh : hasWeakWordDeriv X U I f h)
    (hgn : holderENorm G.d α (U : Set (Fin n → ℝ)) g < ⊤)
    (hhn : holderENorm G.d α (U : Set (Fin n → ℝ)) h < ⊤) :
    EqOn g h (U : Set (Fin n → ℝ)) :=
  Measure.eqOn_open_of_ae_eq (hasWeakWordDeriv_unique X U hg hh) U.isOpen
    (continuousOn_of_holderENorm_lt_top_subset Ω G hU hα hgn)
    (continuousOn_of_holderENorm_lt_top_subset Ω G hU hα hhn)

/-- Every continuous weak word derivative vanishes outside
any closed support set of its input, within the open domain
(BB p. 73 and p. 84; locality). -/
theorem weakHolder_derivative_zero_off_support
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q))
    {α : ℝ} (hα : 0 < α) {f g : (Fin n → ℝ) → ℝ}
    (hg : hasWeakWordDeriv X U I f g)
    (hgn : holderENorm G.d α (U : Set (Fin n → ℝ)) g < ⊤)
    {K : Set (Fin n → ℝ)} (hK : IsClosed K) (hf : ∀ x ∈ (U : Set (Fin n → ℝ)) \ K,f x = 0) :
    ∀ x ∈ (U : Set (Fin n → ℝ)) \ K,g x = 0 := by
  let V : Opens (Fin n → ℝ) := ⟨(U : Set (Fin n → ℝ)) \ K,U.isOpen.sdiff hK⟩
  have hv : (V : Set (Fin n → ℝ)) ⊆ U := fun _ hx => hx.1
  have hfa : f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    exact hf x hx
  have hga := hasWeakWordDeriv_locality X U V hv hg hfa
  exact Measure.eqOn_open_of_ae_eq hga V.isOpen
    ((continuousOn_of_holderENorm_lt_top_subset Ω G hU hα hgn).mono hv) continuousOn_const

end RothschildStein.S

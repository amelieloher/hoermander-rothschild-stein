-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderArithmetic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]

/-- An eventual uniform Hölder bound passes to a pointwise
limit. The factor two comes from bounding the supremum and seminorm
separately and suffices for the Cauchy completeness argument
(BB Prop 2.15, p. 82; direct-limit). -/
theorem holderENorm_limit_le_add_self
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) {α : ℝ} (hα : 0 < α)
    (V : Set (Fin n → ℝ)) (hsep : ∀ x ∈ V,∀ y ∈ V,d x y = 0 → x = y)
    (F : ι → (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hlim : ∀ x ∈ V,Tendsto (fun j => F j x) l (𝓝 (f x)))
    (C : ℝ≥0∞) (hC : C < ⊤) (hb : ∀ᶠ j in l,holderENorm d α V (F j) ≤ C) :
    holderENorm d α V f ≤ C+C := by
  have hn : (⨆ x : V,ENNReal.ofReal |f x.val|) ≤ C := by
    apply iSup_le
    intro x
    apply le_of_tendsto (ENNReal.tendsto_ofReal (hlim x.val x.property).abs)
    filter_upwards [hb] with j hj
    exact (enorm_le_holderENorm d α V (F j) x.property).trans hj
  have hs : holderSeminorm d α V f ≤ C := by
    apply holderSeminorm_le_of_bound d α V f C hC
    intro x hx y hy hd
    apply le_of_tendsto (ENNReal.tendsto_ofReal ((hlim x hx).sub (hlim y hy)).abs)
    filter_upwards [hb] with j hj
    exact (holderSeminorm_increment_le d α V (F j) hα hsep hx hy hd).trans
      (mul_le_mul_left (le_add_self.trans hj) _)
  exact add_le_add hn hs

end RothschildStein.S

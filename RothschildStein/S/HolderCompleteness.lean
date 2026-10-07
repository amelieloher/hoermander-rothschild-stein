-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderCauchy
public import RothschildStein.S.HolderLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- Every Cauchy sequence for the exact Hölder norm
has a finite-norm limit with convergence in that norm. The function
carrier is pointwise on V, so exterior values do not create a false
normed-space assertion (BB Prop 2.15, p. 82; direct Cauchy). -/
theorem exists_holderENorm_limit_of_cauchy
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) {α : ℝ} (hα : 0 < α)
    (V : Set (Fin n → ℝ)) (hsep : ∀ x ∈ V,∀ y ∈ V,d x y = 0 → x = y)
    (F : ℕ → (Fin n → ℝ) → ℝ) (hF : ∀ j,holderENorm d α V (F j) < ⊤)
    (h : holderCauchySeq d α V F) :
    ∃ f : (Fin n → ℝ) → ℝ,holderENorm d α V f < ⊤ ∧
      Tendsto (fun j => holderENorm d α V (fun x => F j x-f x)) atTop (𝓝 0) ∧
      ∀ x ∈ V,Tendsto (fun j => F j x) atTop (𝓝 (f x)) := by
  classical
  have he : ∀ x : V,∃ c : ℝ,Tendsto (fun j => F j x.val) atTop (𝓝 c) := by
    intro x
    exact cauchySeq_tendsto_of_complete (holderCauchySeq_pointwise d α V F h x.property)
  choose c hc using he
  let f := fun x : Fin n → ℝ => if hx : x ∈ V then c ⟨x,hx⟩ else 0
  have hlim : ∀ x ∈ V,Tendsto (fun j => F j x) atTop (𝓝 (f x)) := by
    intro x hx
    simpa only [f,dite_eq_left hx] using! hc ⟨x,hx⟩
  have herr : ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m ≥ N,
      holderENorm d α V (fun x => F m x-f x) ≤ ENNReal.ofReal ε+ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := h ε hε
    refine ⟨N,fun m hm => ?_⟩
    apply holderENorm_limit_le_add_self d hα V hsep
      (fun j x => F m x-F j x) (fun x => F m x-f x)
      (fun x hx => tendsto_const_nhds.sub (hlim x hx))
      (ENNReal.ofReal ε) ENNReal.ofReal_lt_top
    exact eventually_atTop.mpr ⟨N,fun j hj => hN m hm j hj⟩
  have hfinite : holderENorm d α V f < ⊤ := by
    obtain ⟨N,hN⟩ := herr 1 zero_lt_one
    have hE : holderENorm d α V (fun x => F N x-f x) < ⊤ :=
      lt_of_le_of_lt (hN N le_rfl) (by norm_num)
    have H := holderENorm_sub_le d α V hα hsep (F N) (fun x => F N x-f x) (hF N) hE
    have hi : (fun x => F N x-(F N x-f x)) = f := by funext x; ring
    rw [hi] at H
    exact lt_of_le_of_lt H (ENNReal.add_lt_top.mpr ⟨hF N,hE⟩)
  refine ⟨f,hfinite,?_,hlim⟩
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ,hd,hδ⟩ := ENNReal.exists_nnreal_pos_mul_lt (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hε.ne'
  obtain ⟨N,hN⟩ := herr (δ : ℝ) (by exact_mod_cast hd)
  apply eventually_atTop.mpr
  refine ⟨N,fun m hm => (hN m hm).trans ?_⟩
  calc
    ENNReal.ofReal (δ : ℝ)+ENNReal.ofReal (δ : ℝ) = (δ : ℝ≥0∞)*2 := by
      rw [ENNReal.ofReal_coe_nnreal]
      ring
    _ ≤ ε := hδ.le

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- Hölder seminorm on a set, using Mathlib's least Hölder constant.
BB Definition 7.6, p. 298. An infinite value records failure of Hölder boundedness. -/
def holderSemi (δ : ℝ≥0) (A : Set X) (f : X → ℝ) : ℝ≥0∞ :=
  eHolderNorm δ (fun x : A => f x)

/-- Supremum term of the bounded Hölder norm, including the empty set. -/
def holderSup (A : Set X) (f : X → ℝ) : ℝ≥0∞ := ⨆ x : A, ENNReal.ofReal |f x|

/-- The full norm is the supremum plus the Hölder seminorm. -/
def boundedHolderNorm (δ : ℝ≥0) (A : Set X) (f : X → ℝ) : ℝ≥0∞ :=
  holderSup A f + holderSemi δ A f

/-- Membership in the bounded Hölder space is finiteness of its full norm. -/
def BoundedHolder (δ : ℝ≥0) (A : Set X) (f : X → ℝ) : Prop :=
  boundedHolderNorm δ A f < ⊤

/-- The seminorm is bounded by any real pointwise Hölder constant. -/
theorem holderSemi_le_of_bound {δ : ℝ≥0} {A : Set X} {f : X → ℝ} {H : ℝ}
    (hH : 0 ≤ H) (hf : ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ H * dist x y ^ (δ : ℝ)) :
    holderSemi δ A f ≤ ENNReal.ofReal H := by
  have hh : HolderWith (Real.toNNReal H) δ (fun x : A => f x) := by
    intro x y
    simp only [edist_dist, Real.dist_eq, Subtype.dist_eq]
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal' H, max_eq_left hH,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg δ.coe_nonneg, ← ENNReal.ofReal_mul hH]
    exact ENNReal.ofReal_le_ofReal (hf x x.property y y.property)
  simpa [holderSemi, ENNReal.ofReal] using hh.eHolderNorm_le

omit [MetricSpace X] in
/-- The supremum term is bounded by any uniform absolute bound. -/
theorem holderSup_le_of_bound {A : Set X} {f : X → ℝ} {M : ℝ}
    (hf : ∀ x ∈ A, |f x| ≤ M) : holderSup A f ≤ ENNReal.ofReal M :=
  iSup_le fun x => ENNReal.ofReal_le_ofReal (hf x x.property)

omit [MetricSpace X] in
/-- A finite supremum gives its pointwise real bound. -/
theorem abs_le_holderSup {A : Set X} {f : X → ℝ} (hf : holderSup A f < ⊤)
    {x : X} (hx : x ∈ A) : |f x| ≤ (holderSup A f).toReal := by
  have hb : ENNReal.ofReal |f x| ≤ holderSup A f := le_iSup (fun x : A => ENNReal.ofReal |f x|) ⟨x, hx⟩
  simpa [ENNReal.toReal_ofReal (abs_nonneg _)] using ENNReal.toReal_mono hf.ne hb

/-- A finite Hölder seminorm realizes the least pointwise constant. -/
theorem sub_le_holderSemi {δ : ℝ≥0} {A : Set X} {f : X → ℝ}
    (hf : holderSemi δ A f < ⊤) {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    |f x - f y| ≤ (holderSemi δ A f).toReal * dist x y ^ (δ : ℝ) := by
  have hm : MemHolder δ (fun x : A => f x) := eHolderNorm_lt_top.mp hf
  simpa [Real.dist_eq, Subtype.dist_eq, nnHolderNorm, holderSemi, ENNReal.coe_toNNReal_eq_toReal] using
    hm.holderWith.dist_le (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)

/-- The finite full norm controls both of its terms. -/
theorem BoundedHolder.parts {δ : ℝ≥0} {A : Set X} {f : X → ℝ}
    (hf : BoundedHolder δ A f) : holderSup A f < ⊤ ∧ holderSemi δ A f < ⊤ := by
  exact ⟨(le_add_right le_rfl).trans_lt hf, (le_add_left le_rfl).trans_lt hf⟩

end RothschildStein.H2

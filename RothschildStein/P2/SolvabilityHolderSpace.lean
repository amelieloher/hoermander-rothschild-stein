-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderCompleteness
public import RothschildStein.S.HolderListSums
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Local solvability, Hölder contraction: the Banach space `C^α(V)` of bounded Hölder functions

For the Hölder norm `holderENorm d α V f = sup_V |f| + [f]_α` (definition) with a
distance `d` separating the points of `V` and `α > 0`, the functions `f : V → ℝ` of finite norm form
an additive subgroup `HolderData.subgroup` of `V → ℝ`. The carrier is the functions *on* `V`
(exterior values never enter the norm; the completeness convention for the carrier); the norm is
`‖f‖ = (holderENorm d α V f̃).toReal` for the zero extension `f̃` of `f`
(`HolderData.zeroExt`). `BoundedHolder H` is a `NormedAddCommGroup` and, by the completeness
statement `S.exists_holderENorm_limit_of_cauchy` (BB Prop 2.15, p. 82), a
`CompleteSpace`.

The fixed-point statement in the Banach space is `HolderBoundedOperator.exists_function_fixedPoint`
(operators given on functions `E → ℝ`, finite norms, a.e.-replaced by "equal on `V`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RothschildStein.P2

/-- The data of a Hölder space: a distance `d` on `ℝ^N` (values in
`[0, ∞]`), an exponent `α > 0` and a set `V` on which `d` separates points. -/
structure HolderData (N : ℕ) where
  /-- The distance. -/
  d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞
  /-- The Hölder exponent. -/
  α : ℝ
  /-- The domain. -/
  V : Set (Fin N → ℝ)
  /-- The exponent is positive. -/
  α_pos : 0 < α
  /-- `d` separates the points of `V`. -/
  sep : ∀ x ∈ V, ∀ y ∈ V, d x y = 0 → x = y

namespace HolderData

variable {N : ℕ} (H : HolderData N)

open Classical in
/-- The zero extension of a function on `V` to `ℝ^N`. -/
def zeroExt (f : H.V → ℝ) : (Fin N → ℝ) → ℝ := fun x => if h : x ∈ H.V then f ⟨x, h⟩ else 0

/-- The zero extension of `f` agrees with `f` at points of `V`. -/
theorem zeroExt_of_mem (f : H.V → ℝ) {x : Fin N → ℝ} (hx : x ∈ H.V) : H.zeroExt f x = f ⟨x, hx⟩ :=
  by simp [zeroExt, hx]

/-- The zero extension of `0` is `0`. -/
theorem zeroExt_zero : H.zeroExt 0 = fun _ => 0 := by
  funext x
  unfold zeroExt
  split_ifs <;> rfl

/-- The zero extension is additive. -/
theorem zeroExt_add (f g : H.V → ℝ) : H.zeroExt (f + g) = fun x => H.zeroExt f x + H.zeroExt g x := by
  funext x
  unfold zeroExt
  split_ifs <;> simp

/-- The zero extension commutes with negation. -/
theorem zeroExt_neg (f : H.V → ℝ) : H.zeroExt (-f) = fun x => -H.zeroExt f x := by
  funext x
  unfold zeroExt
  split_ifs <;> simp

/-- The zero extension is compatible with subtraction. -/
theorem zeroExt_sub (f g : H.V → ℝ) : H.zeroExt (f - g) = fun x => H.zeroExt f x - H.zeroExt g x := by
  funext x
  unfold zeroExt
  split_ifs <;> simp

/-- The Hölder norm of a function on `V` (through its zero
extension). -/
def hnorm (f : H.V → ℝ) : ℝ≥0∞ := holderENorm H.d H.α H.V (H.zeroExt f)

/-- The functions on `V` of finite Hölder norm form an additive
subgroup of `V → ℝ` (BB Prop 2.15, p. 82). -/
def subgroup : AddSubgroup (H.V → ℝ) where
  carrier := {f | H.hnorm f < ⊤}
  zero_mem' := by
    show H.hnorm 0 < ⊤
    simp [hnorm, zeroExt_zero, S.holderENorm_zero_function]
  add_mem' {f g} hf hg := by
    have hf : H.hnorm f < ⊤ := hf
    have hg : H.hnorm g < ⊤ := hg
    have h := S.holderENorm_add_le H.d H.α H.V H.α_pos H.sep (H.zeroExt f) (H.zeroExt g) hf hg
    show H.hnorm (f + g) < ⊤
    unfold hnorm
    rw [zeroExt_add]
    exact lt_of_le_of_lt h (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)
  neg_mem' {f} hf := by
    have hf : H.hnorm f < ⊤ := hf
    show H.hnorm (-f) < ⊤
    simpa only [hnorm, zeroExt_neg, S.holderENorm_neg] using hf

end HolderData

/-- **The bounded Hölder space** `C^α(V)` of a `HolderData`: the
functions on `V` of finite Hölder norm. -/
def BoundedHolder {N : ℕ} (H : HolderData N) : Type := ↥H.subgroup

namespace BoundedHolder

variable {N : ℕ} {H : HolderData N}

/-- The additive group structure of `BoundedHolder H`. -/
instance instAddCommGroup (H : HolderData N) : AddCommGroup (BoundedHolder H) :=
  inferInstanceAs (AddCommGroup ↥H.subgroup)

/-- The underlying function on `V`. -/
def val (f : BoundedHolder H) : H.V → ℝ := Subtype.val (show ↥H.subgroup from f)

/-- An element of `BoundedHolder H` from a function on `V` of finite
Hölder norm. -/
def mk (f : H.V → ℝ) (hf : H.hnorm f < ⊤) : BoundedHolder H := (⟨f, hf⟩ : ↥H.subgroup)

/-- `mk` and `val` are inverse. -/
@[simp] theorem val_mk (f : H.V → ℝ) (hf : H.hnorm f < ⊤) : (mk f hf).val = f := rfl

/-- An element of `C^α(V)` has finite Hölder norm. -/
theorem hnorm_lt_top (f : BoundedHolder H) : H.hnorm f.val < ⊤ := (show ↥H.subgroup from f).2

/-- An element of `C^α(V)` has Hölder norm different from `∞`. -/
theorem hnorm_ne_top (f : BoundedHolder H) : H.hnorm f.val ≠ ⊤ := f.hnorm_lt_top.ne

/-- Extensionality for `C^α(V)`. -/
theorem ext {f g : BoundedHolder H} (h : f.val = g.val) : f = g :=
  Subtype.ext (show (show ↥H.subgroup from f).1 = (show ↥H.subgroup from g).1 from h)

/-- The zero element is the zero function. -/
@[simp] theorem val_zero : (0 : BoundedHolder H).val = 0 := rfl

/-- Addition is pointwise. -/
theorem val_add (f g : BoundedHolder H) : (f + g).val = f.val + g.val := rfl

/-- Negation is pointwise. -/
theorem val_neg (f : BoundedHolder H) : (-f).val = -f.val := rfl

/-- Subtraction is pointwise. -/
theorem val_sub (f g : BoundedHolder H) : (f - g).val = f.val - g.val := rfl

/-- The norm `‖f‖ = (holderENorm f̃).toReal` as an `AddGroupNorm`. -/
def groupNorm (H : HolderData N) : AddGroupNorm (BoundedHolder H) where
  toFun f := (H.hnorm f.val).toReal
  map_zero' := by
    simp [HolderData.hnorm, HolderData.zeroExt_zero, S.holderENorm_zero_function]
  add_le' f g := by
    have h := S.holderENorm_add_le H.d H.α H.V H.α_pos H.sep (H.zeroExt f.val) (H.zeroExt g.val)
      f.hnorm_lt_top g.hnorm_lt_top
    have h' : H.hnorm (f + g).val ≤ H.hnorm f.val + H.hnorm g.val := by
      rw [val_add]
      unfold HolderData.hnorm
      rw [HolderData.zeroExt_add]
      exact h
    calc (H.hnorm (f + g).val).toReal ≤ (H.hnorm f.val + H.hnorm g.val).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨f.hnorm_ne_top, g.hnorm_ne_top⟩) h'
      _ = (H.hnorm f.val).toReal + (H.hnorm g.val).toReal :=
          ENNReal.toReal_add f.hnorm_ne_top g.hnorm_ne_top
  neg' f := by
    simp only [val_neg, HolderData.hnorm, HolderData.zeroExt_neg, S.holderENorm_neg]
  eq_zero_of_map_eq_zero' f hf := by
    have h0 : H.hnorm f.val = 0 := by
      have := (ENNReal.toReal_eq_zero_iff _).mp hf
      exact this.resolve_right f.hnorm_ne_top
    refine ext (funext fun x => ?_)
    have h1 := S.enorm_le_holderENorm H.d H.α H.V (H.zeroExt f.val) x.2
    rw [show holderENorm H.d H.α H.V (H.zeroExt f.val) = 0 from h0, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero, H.zeroExt_of_mem f.val x.2] at h1
    exact abs_nonpos_iff.mp h1

/-- `BoundedHolder H` is a normed additive group. -/
instance instNormedAddCommGroup : NormedAddCommGroup (BoundedHolder H) :=
  (groupNorm H).toNormedAddCommGroup

/-- The norm of `C^α(V)` is the `toReal` of the Hölder norm of the zero extension. -/
theorem norm_def (f : BoundedHolder H) : ‖f‖ = (H.hnorm f.val).toReal := rfl

/-- The norm of `C^α(V)` is the finite Hölder norm. -/
theorem ofReal_norm_eq_hnorm (f : BoundedHolder H) : ENNReal.ofReal ‖f‖ = H.hnorm f.val :=
  ENNReal.ofReal_toReal f.hnorm_ne_top

/-- The Hölder norm of a difference, in terms of the zero extensions. -/
theorem hnorm_sub (f g : BoundedHolder H) :
    H.hnorm (f - g).val = holderENorm H.d H.α H.V
      (fun x => H.zeroExt f.val x - H.zeroExt g.val x) := by
  rw [val_sub]
  unfold HolderData.hnorm
  rw [HolderData.zeroExt_sub]

/-- **Completeness of the bounded Hölder space** (BB
Prop 2.15, p. 82): the normed space `C^α(V)` is a Banach space. -/
instance instCompleteSpace : CompleteSpace (BoundedHolder H) := by
  refine @Metric.complete_of_cauchySeq_tendsto (BoundedHolder H) _ fun u hu => ?_
  set F : ℕ → (Fin N → ℝ) → ℝ := fun j => H.zeroExt (u j).val with hF
  have hFfin : ∀ j, holderENorm H.d H.α H.V (F j) < ⊤ := fun j => (u j).hnorm_lt_top
  have hc : S.holderCauchySeq H.d H.α H.V F := by
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨M, fun m hm j hj => ?_⟩
    have h1 := hM m hm j hj
    rw [dist_eq_norm, norm_def] at h1
    have h2 : H.hnorm (u m - u j).val ≤ ENNReal.ofReal ε := by
      have := (ENNReal.ofReal_toReal (u m - u j).hnorm_ne_top).symm.le.trans
        (ENNReal.ofReal_le_ofReal h1.le)
      exact this
    rwa [hnorm_sub] at h2
  obtain ⟨f, hf, ht, hpt⟩ := S.exists_holderENorm_limit_of_cauchy H.d H.α_pos H.V H.sep F hFfin hc
  have hfeq : holderENorm H.d H.α H.V (H.zeroExt (fun x : H.V => f x.1)) =
      holderENorm H.d H.α H.V f :=
    S.holderENorm_congr H.d H.α H.V _ (fun x hx => by rw [H.zeroExt_of_mem _ hx])
  have hfv : H.hnorm (fun x : H.V => f x.1) < ⊤ := by
    unfold HolderData.hnorm
    rw [hfeq]
    exact hf
  refine ⟨mk (fun x : H.V => f x.1) hfv, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  rw [ENNReal.toReal_zero] at h0
  refine h0.congr fun j => ?_
  rw [norm_def, hnorm_sub]
  show (holderENorm H.d H.α H.V fun x => F j x - f x).toReal = _
  congr 1
  refine S.holderENorm_congr H.d H.α H.V _ (fun x hx => ?_)
  show F j x - f x = H.zeroExt (u j).val x - H.zeroExt (mk (fun x : H.V => f x.1) hfv).val x
  simp only [val_mk, H.zeroExt_of_mem _ hx, hF]

end BoundedHolder

end RothschildStein.P2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityHolderSpace
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Local solvability, Hölder contraction: the abstract Hölder fixed point `f = g + T f`

An operator `T` on real functions on `ℝ^N` with the three properties of `HolderBoundedOperator`
(`C^α(V)`-norm bound `‖T f‖_{C^α(V)} ≤ Λ ‖f‖_{C^α(V)}`, dependence on the values on `V` only,
additivity on functions of finite norm on `V`) descends to a map `HolderBoundedOperator.map` of the
Banach space `BoundedHolder H = C^α(V)` (`SolvabilityHolderSpace`). If `Λ ≤ 1/2` the map
`f ↦ g + T f` is a contraction (`ContractingWith`), so by Banach's theorem there is a unique
solution `f = g + T f` in `C^α(V)` with `‖f‖_{C^α(V)} ≤ 2 ‖g‖_{C^α(V)}`
(`HolderBoundedOperator.exists_function_fixedPoint`; proof of BB Prop 11.61(b),
last sentence: "Thus `f = g + 𝓕_R f` has a unique solution in the full Banach space `C^α(U_R)`").
The chart instance is in `SolvabilityHolder`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal NNReal
namespace RothschildStein.P2

/-- A **bounded operator of the Hölder space `C^α(V)`**, given on
functions `ℝ^N → ℝ`: `‖T f‖_{C^α(V)} ≤ Λ ‖f‖_{C^α(V)}`, `T f` on `V` only depends on `f` on `V`,
and `T` is additive on `V` for functions of finite norm. -/
structure HolderBoundedOperator {N : ℕ} (H : HolderData N)
    (T : ((Fin N → ℝ) → ℝ) → ((Fin N → ℝ) → ℝ)) (Λ : ℝ) : Prop where
  /-- The norm bound `‖T f‖_{C^α(V)} ≤ Λ ‖f‖_{C^α(V)}`. -/
  norm_le : ∀ f, holderENorm H.d H.α H.V (T f) ≤ ENNReal.ofReal Λ * holderENorm H.d H.α H.V f
  /-- `T f` on `V` only depends on `f` on `V`. -/
  congr : ∀ f g, EqOn f g H.V → EqOn (T f) (T g) H.V
  /-- `T` is additive on `V` for functions of finite norm. -/
  sub : ∀ f g, holderENorm H.d H.α H.V f < ⊤ → holderENorm H.d H.α H.V g < ⊤ →
    EqOn (T (fun x => f x - g x)) (fun x => T f x - T g x) H.V

namespace HolderData

variable {N : ℕ} (H : HolderData N)

/-- The zero extension of the restriction of `g` to `V` agrees with `g` on `V`. -/
theorem zeroExt_restrict_eqOn (g : (Fin N → ℝ) → ℝ) :
    EqOn (H.zeroExt (fun x : H.V => g x.1)) g H.V := fun _ hx => H.zeroExt_of_mem _ hx

/-- The Hölder norm of the restriction of `g` to `V` is the `holderENorm` of `g`. -/
theorem hnorm_restrict (g : (Fin N → ℝ) → ℝ) :
    H.hnorm (fun x : H.V => g x.1) = holderENorm H.d H.α H.V g :=
  S.holderENorm_congr H.d H.α H.V _ (H.zeroExt_restrict_eqOn g)

end HolderData

namespace BoundedHolder

variable {N : ℕ} {H : HolderData N} {T : ((Fin N → ℝ) → ℝ) → ((Fin N → ℝ) → ℝ)} {Λ : ℝ}

/-- The restriction to `V` of a function of finite Hölder norm, as an
element of `C^α(V)`. -/
def ofFun (g : (Fin N → ℝ) → ℝ) (hg : holderENorm H.d H.α H.V g < ⊤) : BoundedHolder H :=
  mk (fun x : H.V => g x.1) (by rw [H.hnorm_restrict]; exact hg)

/-- The underlying function of `BoundedHolder.ofFun g` is the restriction of `g`. -/
@[simp] theorem val_ofFun (g : (Fin N → ℝ) → ℝ) (hg : holderENorm H.d H.α H.V g < ⊤) (x : H.V) :
    (ofFun g hg).val x = g x.1 := rfl

end BoundedHolder

namespace HolderBoundedOperator

variable {N : ℕ} {H : HolderData N} {T : ((Fin N → ℝ) → ℝ) → ((Fin N → ℝ) → ℝ)} {Λ : ℝ}

/-- `T` maps functions of finite `C^α(V)`-norm to functions of finite `C^α(V)`-norm. -/
theorem map_finite (hT : HolderBoundedOperator H T Λ) (f : BoundedHolder H) :
    H.hnorm (fun x : H.V => T (H.zeroExt f.val) x.1) < ⊤ := by
  rw [H.hnorm_restrict]
  exact lt_of_le_of_lt (hT.norm_le _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top f.hnorm_lt_top)

/-- The operator `T` on the Banach space `C^α(V)`. -/
def map (hT : HolderBoundedOperator H T Λ) (f : BoundedHolder H) : BoundedHolder H :=
  BoundedHolder.mk (fun x : H.V => T (H.zeroExt f.val) x.1) (hT.map_finite f)

/-- The underlying function of `T f` on `V`. -/
theorem val_map (hT : HolderBoundedOperator H T Λ) (f : BoundedHolder H) (x : H.V) :
    (hT.map f).val x = T (H.zeroExt f.val) x.1 := rfl

/-- `T` is additive on `C^α(V)`. -/
theorem map_sub (hT : HolderBoundedOperator H T Λ) (f f' : BoundedHolder H) :
    hT.map (f - f') = hT.map f - hT.map f' := by
  refine BoundedHolder.ext (funext fun x => ?_)
  rw [BoundedHolder.val_sub, Pi.sub_apply, val_map, val_map, val_map, BoundedHolder.val_sub,
    H.zeroExt_sub]
  exact hT.sub _ _ f.hnorm_lt_top f'.hnorm_lt_top x.2

/-- The operator norm bound `‖T f‖ ≤ Λ ‖f‖` on `C^α(V)`. -/
theorem norm_map_le (hT : HolderBoundedOperator H T Λ) (hΛ : 0 ≤ Λ) (f : BoundedHolder H) :
    ‖hT.map f‖ ≤ Λ * ‖f‖ := by
  rw [BoundedHolder.norm_def, BoundedHolder.norm_def]
  have h1 : H.hnorm (hT.map f).val ≤ ENNReal.ofReal Λ * H.hnorm f.val := by
    show H.hnorm (fun x : H.V => T (H.zeroExt f.val) x.1) ≤ _
    rw [H.hnorm_restrict]
    exact hT.norm_le _
  have h2 : ENNReal.ofReal Λ * H.hnorm f.val ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top f.hnorm_ne_top
  calc (H.hnorm (hT.map f).val).toReal ≤ (ENNReal.ofReal Λ * H.hnorm f.val).toReal :=
        ENNReal.toReal_mono h2 h1
    _ = Λ * (H.hnorm f.val).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ]

/-- For `0 ≤ Λ ≤ K < 1`, `f ↦ g + T f` is a contraction of the Banach
space `C^α(V)` with the constant `K`. -/
theorem contractingWith (hT : HolderBoundedOperator H T Λ) (hΛ : 0 ≤ Λ) {K : ℝ≥0}
    (hΛK : Λ ≤ K) (hK1 : K < 1) (g : BoundedHolder H) :
    ContractingWith K (fun f => g + hT.map f) := by
  refine ⟨hK1, LipschitzWith.of_dist_le_mul fun f f' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← hT.map_sub]
  exact (hT.norm_map_le hΛ (f - f')).trans (mul_le_mul_of_nonneg_right hΛK (norm_nonneg _))

/-- **The Hölder fixed point in the Banach space `C^α(V)`.** If
`0 ≤ Λ ≤ 1/2`, for every `g ∈ C^α(V)` the equation `f = g + T f` has a solution `f ∈ C^α(V)`
with `‖f‖ ≤ 2 ‖g‖`, and every solution equals `f`. -/
theorem exists_fixedPoint (hT : HolderBoundedOperator H T Λ) (hΛ : 0 ≤ Λ) (hΛ2 : Λ ≤ 1 / 2)
    (g : BoundedHolder H) :
    ∃ f : BoundedHolder H, (f = g + hT.map f ∧ ‖f‖ ≤ 2 * ‖g‖) ∧
      ∀ f' : BoundedHolder H, f' = g + hT.map f' → f' = f := by
  have hc := hT.contractingWith hΛ (K := 1 / 2) (by simpa using hΛ2) (by
    rw [← NNReal.coe_lt_coe]; norm_num) g
  set f := ContractingWith.fixedPoint _ hc with hf
  have hfix : f = g + hT.map f := (ContractingWith.fixedPoint_isFixedPt (hf := hc)).symm
  have hnorm : ‖f‖ ≤ 2 * ‖g‖ := by
    have h1 : ‖f‖ ≤ ‖g‖ + Λ * ‖f‖ := by
      calc ‖f‖ = ‖g + hT.map f‖ := by rw [← hfix]
        _ ≤ ‖g‖ + ‖hT.map f‖ := norm_add_le _ _
        _ ≤ ‖g‖ + Λ * ‖f‖ := by gcongr; exact hT.norm_map_le hΛ f
    nlinarith [norm_nonneg f, norm_nonneg g]
  exact ⟨f, ⟨hfix, hnorm⟩, fun f' hf' => ContractingWith.fixedPoint_unique hc hf'.symm⟩

/-- **The Hölder fixed point, in terms of functions.** If
`0 ≤ Λ ≤ 1/2` and `g : ℝ^N → ℝ` has finite norm `‖g‖_{C^α(V)}`, there is `f` of finite norm with
`f = g + T f` on `V` and `‖f‖_{C^α(V)} ≤ 2 ‖g‖_{C^α(V)}`; every `f'` of finite norm with
`f' = g + T f'` on `V` equals `f` on `V`. -/
theorem exists_function_fixedPoint (hT : HolderBoundedOperator H T Λ) (hΛ : 0 ≤ Λ)
    (hΛ2 : Λ ≤ 1 / 2) {g : (Fin N → ℝ) → ℝ} (hg : holderENorm H.d H.α H.V g < ⊤) :
    ∃ f : (Fin N → ℝ) → ℝ, holderENorm H.d H.α H.V f < ⊤ ∧
      EqOn f (fun x => g x + T f x) H.V ∧
      holderENorm H.d H.α H.V f ≤ 2 * holderENorm H.d H.α H.V g ∧
      ∀ f' : (Fin N → ℝ) → ℝ, holderENorm H.d H.α H.V f' < ⊤ →
        EqOn f' (fun x => g x + T f' x) H.V → EqOn f' f H.V := by
  set gB : BoundedHolder H := BoundedHolder.ofFun g hg with hgB
  obtain ⟨fB, ⟨hfix, hnorm⟩, huniq⟩ := hT.exists_fixedPoint hΛ hΛ2 gB
  refine ⟨H.zeroExt fB.val, fB.hnorm_lt_top, fun x hx => ?_, ?_, fun f' hf' hf'fix => ?_⟩
  · have h1 := congrFun (congrArg BoundedHolder.val hfix) ⟨x, hx⟩
    rw [BoundedHolder.val_add, Pi.add_apply, val_map] at h1
    rw [H.zeroExt_of_mem _ hx, h1]
    rfl
  · have h1 : H.hnorm fB.val ≤ 2 * H.hnorm gB.val := by
      have := ENNReal.ofReal_le_ofReal hnorm
      rwa [ENNReal.ofReal_mul (by norm_num), BoundedHolder.ofReal_norm_eq_hnorm,
        BoundedHolder.ofReal_norm_eq_hnorm, ENNReal.ofReal_ofNat] at this
    have h2 : H.hnorm gB.val = holderENorm H.d H.α H.V g := H.hnorm_restrict g
    rw [h2] at h1
    exact h1
  · set f'B : BoundedHolder H := BoundedHolder.ofFun f' hf' with hf'B
    have hext : EqOn (H.zeroExt f'B.val) f' H.V := H.zeroExt_restrict_eqOn f'
    have hfx : f'B = gB + hT.map f'B := by
      refine BoundedHolder.ext (funext fun x => ?_)
      rw [BoundedHolder.val_add, Pi.add_apply, val_map]
      show f' x.1 = g x.1 + T (H.zeroExt f'B.val) x.1
      rw [hT.congr _ _ hext x.2]
      exact hf'fix x.2
    have := huniq f'B hfx
    intro x hx
    have h1 := congrFun (congrArg BoundedHolder.val this) ⟨x, hx⟩
    rw [H.zeroExt_of_mem _ hx]
    exact h1

end HolderBoundedOperator

end RothschildStein.P2

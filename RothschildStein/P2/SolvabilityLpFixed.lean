-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Local solvability, `L^p` contraction: the abstract `L^p` fixed point `f = g + T f`

An operator `T` on real functions with the four properties of `LpBoundedOperator` (it maps
`L^p(ν)` into itself with `‖T f‖_p ≤ Λ ‖f‖_p`, is insensitive to null sets, and is additive on
`L^p` up to null sets) descends to a map `LpBoundedOperator.toLp` of the Banach space
`Lp ℝ p ν`. If `Λ ≤ 1/2`, the map `f ↦ g + T f` is a contraction of `Lp ℝ p ν`
(`ContractingWith`), so by Banach's theorem (Mathlib `ContractingWith.fixedPoint`) there is a
unique solution `f = g + T f`, and `‖f‖_p ≤ 2 ‖g‖_p` (BB p. 605, proof of
Prop 11.61(a), after the displayed kernel bounds).

The chart instance (`T = 𝓕_r`, the restricted error of `F_R^chart`) is in `SolvabilityLp`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open MeasureTheory Function
open scoped ENNReal NNReal
namespace RothschildStein.P2

variable {E : Type*} [MeasurableSpace E]

/-- A **bounded `L^p`-operator on functions** `T : (E → ℝ) → (E → ℝ)`
with norm at most `Λ`: it maps `L^p(ν)` into itself with `‖T f‖_p ≤ Λ ‖f‖_p`, depends only on the
`ν`-a.e. class of `f`, and is linear up to null sets on `L^p`. (An integral operator with a
kernel integrable in the sense of Schur is of this kind: the integral is linear wherever it
converges absolutely, which is almost everywhere.) -/
structure LpBoundedOperator (ν : Measure E) (p : ℝ≥0∞) (T : (E → ℝ) → (E → ℝ)) (Λ : ℝ) :
    Prop where
  /-- `T` maps `L^p` into `L^p`. -/
  memLp : ∀ f, MemLp f p ν → MemLp (T f) p ν
  /-- The norm bound `‖T f‖_p ≤ Λ ‖f‖_p`. -/
  norm_le : ∀ f, MemLp f p ν → eLpNorm (T f) p ν ≤ ENNReal.ofReal Λ * eLpNorm f p ν
  /-- `T f` only depends on the a.e. class of `f`. -/
  ae_congr : ∀ f g, f =ᵐ[ν] g → T f =ᵐ[ν] T g
  /-- `T` is additive on `L^p` up to null sets. -/
  ae_sub : ∀ f g, MemLp f p ν → MemLp g p ν → T (f - g) =ᵐ[ν] T f - T g
  /-- `T` is homogeneous on `L^p` up to null sets. -/
  ae_smul : ∀ (c : ℝ) f, MemLp f p ν → T (c • f) =ᵐ[ν] c • T f

namespace LpBoundedOperator

variable {ν : Measure E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {T : (E → ℝ) → (E → ℝ)} {Λ : ℝ}

omit [Fact (1 ≤ p)] in
/-- Being a bounded `L^p`-operator only depends on the a.e. class of
`T f` for each `f`. -/
theorem congr_ae {T' : (E → ℝ) → (E → ℝ)} (hT : LpBoundedOperator ν p T Λ)
    (h : ∀ f, T' f =ᵐ[ν] T f) : LpBoundedOperator ν p T' Λ where
  memLp f hf := (hT.memLp f hf).ae_eq (h f).symm
  norm_le f hf := (eLpNorm_congr_ae (h f)).trans_le (hT.norm_le f hf)
  ae_congr f g hfg := (h f).trans ((hT.ae_congr f g hfg).trans (h g).symm)
  ae_sub f g hf hg := (h (f - g)).trans ((hT.ae_sub f g hf hg).trans ((h f).symm.sub (h g).symm))
  ae_smul c f hf := (h (c • f)).trans ((hT.ae_smul c f hf).trans ((h f).symm.const_smul c))

/-- The operator `T` on the Banach space `Lp ℝ p ν`. -/
def toLp (hT : LpBoundedOperator ν p T Λ) (f : Lp ℝ p ν) : Lp ℝ p ν :=
  (hT.memLp f (Lp.memLp f)).toLp (T f)

omit [Fact (1 ≤ p)] in
/-- A representative of `T f` in `Lp ℝ p ν` is `T ⇑f`. -/
theorem coeFn_toLp (hT : LpBoundedOperator ν p T Λ) (f : Lp ℝ p ν) :
    ⇑(hT.toLp f) =ᵐ[ν] T f :=
  MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
/-- `T` is additive on `Lp ℝ p ν`. -/
theorem toLp_sub (hT : LpBoundedOperator ν p T Λ) (f f' : Lp ℝ p ν) :
    hT.toLp (f - f') = hT.toLp f - hT.toLp f' := by
  refine Lp.ext ?_
  have h1 : T ⇑(f - f') =ᵐ[ν] T (⇑f - ⇑f') := hT.ae_congr _ _ (Lp.coeFn_sub f f')
  have h2 := hT.ae_sub f f' (Lp.memLp f) (Lp.memLp f')
  filter_upwards [hT.coeFn_toLp (f - f'), h1, h2, Lp.coeFn_sub (hT.toLp f) (hT.toLp f'),
    hT.coeFn_toLp f, hT.coeFn_toLp f'] with x hx1 hx2 hx3 hx4 hx5 hx6
  rw [hx1, hx2, hx3, hx4]
  simp [hx5, hx6]

omit [Fact (1 ≤ p)] in
/-- `T` maps `0` to `0` on `Lp ℝ p ν`. -/
theorem toLp_zero (hT : LpBoundedOperator ν p T Λ) : hT.toLp 0 = 0 := by
  refine Lp.ext ?_
  have h0 : (0 : E → ℝ) - 0 = 0 := sub_self _
  have h1 := hT.ae_sub 0 0 (MemLp.zero) (MemLp.zero)
  rw [h0] at h1
  have h2 : T ⇑(0 : Lp ℝ p ν) =ᵐ[ν] T 0 := hT.ae_congr _ _ (Lp.coeFn_zero ℝ p ν)
  filter_upwards [hT.coeFn_toLp 0, h2, h1, Lp.coeFn_zero ℝ p ν] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hx4]
  simp

omit [Fact (1 ≤ p)] in
/-- `T` commutes with negation on `Lp ℝ p ν`. -/
theorem toLp_neg (hT : LpBoundedOperator ν p T Λ) (f : Lp ℝ p ν) :
    hT.toLp (-f) = -hT.toLp f := by
  have := hT.toLp_sub 0 f
  rwa [zero_sub, hT.toLp_zero, zero_sub] at this

omit [Fact (1 ≤ p)] in
/-- `T` is additive on `Lp ℝ p ν`. -/
theorem toLp_add (hT : LpBoundedOperator ν p T Λ) (f f' : Lp ℝ p ν) :
    hT.toLp (f + f') = hT.toLp f + hT.toLp f' := by
  have := hT.toLp_sub f (-f')
  rwa [sub_neg_eq_add, hT.toLp_neg, sub_neg_eq_add] at this

omit [Fact (1 ≤ p)] in
/-- `T` is homogeneous on `Lp ℝ p ν`. -/
theorem toLp_smul (hT : LpBoundedOperator ν p T Λ) (c : ℝ) (f : Lp ℝ p ν) :
    hT.toLp (c • f) = c • hT.toLp f := by
  refine Lp.ext ?_
  have h1 : T ⇑(c • f) =ᵐ[ν] T (c • ⇑f) := hT.ae_congr _ _ (Lp.coeFn_smul c f)
  have h2 := hT.ae_smul c f (Lp.memLp f)
  filter_upwards [hT.coeFn_toLp (c • f), h1, h2, Lp.coeFn_smul c (hT.toLp f),
    hT.coeFn_toLp f] with x hx1 hx2 hx3 hx4 hx5
  rw [hx1, hx2, hx3, hx4]
  simp [hx5]

omit [Fact (1 ≤ p)] in
/-- The operator norm bound `‖T f‖ ≤ Λ ‖f‖` on `Lp ℝ p ν`. -/
theorem norm_toLp_le (hT : LpBoundedOperator ν p T Λ) (hΛ : 0 ≤ Λ) (f : Lp ℝ p ν) :
    ‖hT.toLp f‖ ≤ Λ * ‖f‖ := by
  unfold toLp
  rw [Lp.norm_toLp, Lp.norm_def]
  have h1 := hT.norm_le f (Lp.memLp f)
  have h2 : ENNReal.ofReal Λ * eLpNorm f p ν ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)
  calc (eLpNorm (T ⇑f) p ν).toReal ≤ (ENNReal.ofReal Λ * eLpNorm (⇑f) p ν).toReal :=
        ENNReal.toReal_mono h2 h1
    _ = Λ * (eLpNorm (⇑f) p ν).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ]

/-- The operator `T` as a continuous linear map of the Banach space
`Lp ℝ p ν`, of norm at most `Λ`. -/
def toCLM (hT : LpBoundedOperator ν p T Λ) (hΛ : 0 ≤ Λ) : Lp ℝ p ν →L[ℝ] Lp ℝ p ν :=
  LinearMap.mkContinuous
    { toFun := hT.toLp
      map_add' := hT.toLp_add
      map_smul' := fun c f => hT.toLp_smul c f } Λ (hT.norm_toLp_le hΛ)

/-- For `0 ≤ Λ ≤ K < 1`, `f ↦ g + T f` is a contraction of `Lp ℝ p ν` with
the constant `K`. -/
theorem contractingWith (hT : LpBoundedOperator ν p T Λ) (hΛ : 0 ≤ Λ) {K : ℝ≥0}
    (hΛK : Λ ≤ K) (hK1 : K < 1) (g : Lp ℝ p ν) :
    ContractingWith K (fun f => g + hT.toLp f) := by
  refine ⟨hK1, LipschitzWith.of_dist_le_mul fun f f' => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← hT.toLp_sub]
  exact (hT.norm_toLp_le hΛ (f - f')).trans (mul_le_mul_of_nonneg_right hΛK (norm_nonneg _))

/-- **The `L^p` fixed point.** If `0 ≤ Λ ≤ 1/2`, for every `g ∈ L^p(ν)` the
equation `f = g + T f` has a solution `f ∈ L^p(ν)` with `‖f‖_p ≤ 2 ‖g‖_p`, and every solution
`f' ∈ L^p(ν)` of the equation is equal to `f`. -/
theorem exists_fixedPoint (hT : LpBoundedOperator ν p T Λ) (hΛ : 0 ≤ Λ) (hΛ2 : Λ ≤ 1 / 2)
    (g : Lp ℝ p ν) :
    ∃ f : Lp ℝ p ν, (f = g + hT.toLp f ∧ ‖f‖ ≤ 2 * ‖g‖) ∧
      ∀ f' : Lp ℝ p ν, f' = g + hT.toLp f' → f' = f := by
  have hc := hT.contractingWith hΛ (K := 1 / 2) (by simpa using hΛ2) (by
    rw [← NNReal.coe_lt_coe]; norm_num) g
  set f := ContractingWith.fixedPoint _ hc with hf
  have hfix : f = g + hT.toLp f := (ContractingWith.fixedPoint_isFixedPt (hf := hc)).symm
  have hnorm : ‖f‖ ≤ 2 * ‖g‖ := by
    have h1 : ‖f‖ ≤ ‖g‖ + Λ * ‖f‖ := by
      calc ‖f‖ = ‖g + hT.toLp f‖ := by rw [← hfix]
        _ ≤ ‖g‖ + ‖hT.toLp f‖ := norm_add_le _ _
        _ ≤ ‖g‖ + Λ * ‖f‖ := by gcongr; exact hT.norm_toLp_le hΛ f
    nlinarith [norm_nonneg f, norm_nonneg g]
  refine ⟨f, ⟨hfix, hnorm⟩, fun f' hf' => ?_⟩
  exact ContractingWith.fixedPoint_unique hc hf'.symm

/-- **The `L^p` fixed point, in terms of functions.** If `0 ≤ Λ ≤ 1/2` and
`g ∈ L^p(ν)`, there is `f ∈ L^p(ν)` with `f = g + T f` almost everywhere and
`‖f‖_p ≤ 2 ‖g‖_p`; every `f' ∈ L^p(ν)` with `f' = g + T f'` almost everywhere equals `f` almost
everywhere. -/
theorem exists_function_fixedPoint (hT : LpBoundedOperator ν p T Λ) (hΛ : 0 ≤ Λ)
    (hΛ2 : Λ ≤ 1 / 2) {g : E → ℝ} (hg : MemLp g p ν) :
    ∃ f : E → ℝ, MemLp f p ν ∧ f =ᵐ[ν] (fun x => g x + T f x) ∧
      eLpNorm f p ν ≤ 2 * eLpNorm g p ν ∧
      ∀ f' : E → ℝ, MemLp f' p ν → f' =ᵐ[ν] (fun x => g x + T f' x) → f' =ᵐ[ν] f := by
  set gL : Lp ℝ p ν := hg.toLp g with hgL
  obtain ⟨fL, ⟨hfix, hnorm⟩, huniq⟩ := hT.exists_fixedPoint hΛ hΛ2 gL
  have hgae : ⇑gL =ᵐ[ν] g := MemLp.coeFn_toLp hg
  refine ⟨⇑fL, Lp.memLp fL, ?_, ?_, fun f' hf' hf'fix => ?_⟩
  · have h1 : ⇑fL =ᵐ[ν] ⇑(gL + hT.toLp fL) := by rw [← hfix]
    filter_upwards [h1, Lp.coeFn_add gL (hT.toLp fL), hgae, hT.coeFn_toLp fL] with x hx1 hx2 hx3 hx4
    rw [hx1, hx2]
    simp [hx3, hx4]
  · have h1 : ‖fL‖ₑ ≤ 2 * ‖gL‖ₑ := by
      have := ENNReal.ofReal_le_ofReal hnorm
      rwa [ENNReal.ofReal_mul (by norm_num), ofReal_norm, ofReal_norm,
        ENNReal.ofReal_ofNat] at this
    rw [Lp.enorm_def, Lp.enorm_def] at h1
    rwa [eLpNorm_congr_ae hgae] at h1
  · set f'L : Lp ℝ p ν := hf'.toLp f' with hf'L
    have hf'ae : ⇑f'L =ᵐ[ν] f' := MemLp.coeFn_toLp hf'
    have hfx : f'L = gL + hT.toLp f'L := by
      refine Lp.ext ?_
      have h1 : T ⇑f'L =ᵐ[ν] T f' := hT.ae_congr _ _ hf'ae
      filter_upwards [Lp.coeFn_add gL (hT.toLp f'L), hgae, hT.coeFn_toLp f'L, hf'ae, hf'fix, h1]
        with x hx1 hx2 hx3 hx4 hx5 hx6
      rw [hx1]
      simp only [Pi.add_apply]
      rw [hx2, hx3, hx6]
      exact hx4.trans hx5
    have := huniq f'L hfx
    filter_upwards [hf'ae] with x hx
    rw [← hx, this]

end LpBoundedOperator

end RothschildStein.P2

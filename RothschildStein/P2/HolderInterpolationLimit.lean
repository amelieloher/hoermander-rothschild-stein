-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationEuclid
public import RothschildStein.P1.ContinuityRegularAssembly
public import RothschildStein.S.HolderLimits
public import RothschildStein.S.HolderBounds

/-!
# Passing the first Hölder interpolation inequality to uniform limits

The first Hölder interpolation inequality (`FractionalInterpolation*`) is proved for functions that
are `C²` in Euclidean coordinates on the chart domain. A compactly supported intrinsic `C^{2,α}`
input `v` of the patch `V` is, by BB Thm 2.20 (`compact_uniform_weak_word_mollification`), the
uniform limit of its Euclidean mollifications `φ_ε` together with their weighted derivatives of weight
at most two (in particular `L̃ φ_ε → L̃ v` uniformly on `V`). This module proves the limit passage in
abstract form: a positive-type operator `T` of a lifted frame is `L^∞`-continuous (the continuity theorem), so
`T (L̃ φ_ε) → T (L̃ v)` pointwise on `V`, the Hölder norm passes to pointwise limits with
a factor two (`S.holderENorm_limit_le_add_self`), and the right-hand sides converge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Generic

variable {E : Type*}

/-- A sup norm of absolute values is stable under a uniform error. -/
theorem iSup_ofReal_abs_le_add {V : Set E} (a b : E → ℝ) {η : ℝ}
    (h : ∀ x ∈ V, |a x - b x| ≤ η) :
    (⨆ x : V, ENNReal.ofReal |a x|) ≤ (⨆ x : V, ENNReal.ofReal |b x|) + ENNReal.ofReal η := by
  refine iSup_le fun x => ?_
  have hx := h x x.2
  have hη : 0 ≤ η := (abs_nonneg _).trans hx
  have h1 : |a x| ≤ |b x| + η := by
    calc |a x| = |b x + (a x - b x)| := by congr 1; ring
      _ ≤ |b x| + |a x - b x| := abs_add_le _ _
      _ ≤ |b x| + η := by linarith
  calc ENNReal.ofReal |a x| ≤ ENNReal.ofReal (|b x| + η) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal |b x| + ENNReal.ofReal η := ENNReal.ofReal_add (abs_nonneg _) hη
    _ ≤ _ := add_le_add (le_iSup (fun y : V => ENNReal.ofReal |b y|) x) le_rfl

/-- Uniform convergence of finitely many families gives uniform convergence of their sum (eventual
form). -/
theorem eventually_abs_sum_sub_le {ι : Type*} {l : Filter ι} {V : Set E} {q : ℕ}
    (A : Fin q → ι → E → ℝ) (a : Fin q → E → ℝ)
    (h : ∀ i, TendstoUniformlyOn (A i) (a i) l V) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in l, ∀ x ∈ V, |∑ i, A i j x - ∑ i, a i x| ≤ η := by
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have h' : ∀ i, ∀ᶠ j in l, ∀ x ∈ V, |A i j x - a i x| < η / ((q : ℝ) + 1) := fun i => by
    have := (Metric.tendstoUniformlyOn_iff.1 (h i)) (η / ((q : ℝ) + 1)) (by positivity)
    filter_upwards [this] with j hj x hx
    have := hj x hx
    rwa [Real.dist_eq, abs_sub_comm] at this
  filter_upwards [Filter.eventually_all.2 h'] with j hj x hx
  calc |∑ i, A i j x - ∑ i, a i x| = |∑ i, (A i j x - a i x)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |A i j x - a i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin q, η / ((q : ℝ) + 1) := Finset.sum_le_sum fun i _ => (hj i x hx).le
    _ = (q : ℝ) * (η / ((q : ℝ) + 1)) := by simp
    _ ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ hq]
        nlinarith

/-- Uniform convergence on `V` as an eventual uniform bound. -/
theorem eventually_abs_sub_le_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι} {V : Set E}
    {A : ι → E → ℝ} {a : E → ℝ} (h : TendstoUniformlyOn A a l V) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j in l, ∀ x ∈ V, |A j x - a x| ≤ η := by
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 h) η hη] with j hj x hx
  have := hj x hx
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this.le

/-- If `A ≤ ofReal (Y + κ η)` for every `η > 0` then `A ≤ ofReal Y`. -/
theorem le_ofReal_of_forall_pos {A : ℝ≥0∞} {Y κ : ℝ}
    (h : ∀ η : ℝ, 0 < η → A ≤ ENNReal.ofReal (Y + κ * η)) : A ≤ ENNReal.ofReal Y := by
  have ht : Tendsto (fun η : ℝ => ENNReal.ofReal (Y + κ * η)) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal Y)) := by
    have h0 : Tendsto (fun η : ℝ => Y + κ * η) (𝓝 (0 : ℝ)) (𝓝 (Y + κ * 0)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
    rw [mul_zero, add_zero] at h0
    exact ENNReal.tendsto_ofReal (h0.mono_left nhdsWithin_le_nhds)
  exact ge_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact h η hη)

end Generic

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The control distance separates points of the patch.** -/
theorem dl_separates (hF : C.IsLiftedFrame F) (hw : ∀ i, (w i : ℕ) ≤ 2) :
    ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)),
      C.dl x y = 0 → x = y := by
  obtain ⟨CE, -, hCE⟩ := exists_norm_le_mul_dl C hw hF.isCompact_closure hF.closure_subset
  intro x hx y hy hxy
  have h := hCE x (subset_closure hx) y (subset_closure hy)
  rw [hxy, ENNReal.toReal_zero, mul_zero] at h
  have : ‖y - x‖ = 0 := le_antisymm h (norm_nonneg _)
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

/-- **Limit passage for the first interpolation inequality.**
Let `T` be a positive-type operator of a lifted frame and `L` an operator on functions. Suppose the
bound `‖T (L φ_ε)‖_{C^α(V)} ≤ ε' ‖L φ_ε‖_{∞,V} + c' ‖φ_ε‖_{∞,V}` holds for the approximants `φ_ε`
(`ε → 0+`), that `L φ_ε → g` and `φ_ε → v` uniformly on the patch `V` and `g` is continuous on `V`.
Then `‖T g‖_{C^α(V)} ≤ 2 ε' ‖g‖_{∞,V} + 2 c' ‖v‖_{∞,V}`. -/
theorem holderENorm_apply_le_of_approx (hF : C.IsLiftedFrame F) (hw : ∀ i, (w i : ℕ) ≤ 2)
    {lam : ℕ} (hlam : 1 ≤ lam) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α)
    {L : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {ε' c' : ℝ} (hε' : 0 < ε') (hc' : 0 < c')
    (φ : ℝ → (Fin (n + m) → ℝ) → ℝ) (g v : (Fin (n + m) → ℝ) → ℝ)
    (hφ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => T.apply (L (φ ε)) x) ≤
        ENNReal.ofReal ε' * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |L (φ ε) x|) +
          ENNReal.ofReal c' * ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |φ ε x|)
    (hLc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (L (φ ε)) (F.V : Set (Fin (n + m) → ℝ)))
    (hg : ContinuousOn g (F.V : Set (Fin (n + m) → ℝ)))
    (hL : TendstoUniformlyOn (fun ε => L (φ ε)) g (𝓝[>] (0 : ℝ))
      (F.V : Set (Fin (n + m) → ℝ)))
    (hv : TendstoUniformlyOn φ v (𝓝[>] (0 : ℝ)) (F.V : Set (Fin (n + m) → ℝ))) :
    holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (T.apply g) ≤
      ENNReal.ofReal (2 * ε') * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |g x|) +
        ENNReal.ofReal (2 * c') * ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x| := by
  set V : Set (Fin (n + m) → ℝ) := (F.V : Set (Fin (n + m) → ℝ)) with hVdef
  have hlam0 : lam ≠ 0 := by omega
  set Sg : ℝ≥0∞ := ⨆ x : V, ENNReal.ofReal |g x| with hSg
  set Sv : ℝ≥0∞ := ⨆ x : V, ENNReal.ofReal |v x| with hSv
  by_cases hSgT : Sg = ⊤
  · rw [hSgT, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by linarith)).ne', top_add]
    exact le_top
  by_cases hSvT : Sv = ⊤
  · rw [hSvT, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by linarith)).ne', add_top]
    exact le_top
  set Mg : ℝ := Sg.toReal with hMg
  set Mv : ℝ := Sv.toReal with hMv
  have hMg0 : 0 ≤ Mg := ENNReal.toReal_nonneg
  have hMv0 : 0 ≤ Mv := ENNReal.toReal_nonneg
  have hgb : ∀ y ∈ V, |g y| ≤ Mg := fun y hy =>
    (ENNReal.ofReal_le_iff_le_toReal hSgT).mp
      (le_iSup (fun x : V => ENNReal.ofReal |g x|) ⟨y, hy⟩)
  have eg : Sg = ENNReal.ofReal Mg := (ENNReal.ofReal_toReal hSgT).symm
  have ev : Sv = ENNReal.ofReal Mv := (ENNReal.ofReal_toReal hSvT).symm
  have hVm : MeasurableSet V := F.V.isOpen.measurableSet
  obtain ⟨Cs, hCs, hsup⟩ := TypeOperator.exists_sup_bound hF hlam T
  have hsep := dl_separates hF hw
  -- integrability of rows and the Lipschitz estimate in the sup norm
  have key : ∀ (x : Fin (n + m) → ℝ) (g1 g2 : (Fin (n + m) → ℝ) → ℝ),
      AEStronglyMeasurable g1 (volume.restrict V) → AEStronglyMeasurable g2 (volume.restrict V) →
      ∀ M1 M2 : ℝ, 0 ≤ M1 → 0 ≤ M2 → (∀ y ∈ V, |g1 y| ≤ M1) → (∀ y ∈ V, |g2 y| ≤ M2) →
      ∀ M : ℝ, 0 ≤ M → (∀ y ∈ V, |g1 y - g2 y| ≤ M) →
        |T.apply g1 x - T.apply g2 x| ≤ Cs * M := by
    intro x g1 g2 hm1 hm2 M1 M2 hM1 hM2 hb1 hb2 M hM hb
    have i1 := TypeOperator.integrable_row hF hlam T hm1 hM1 hb1 x
    have i2 := TypeOperator.integrable_row hF hlam T hm2 hM2 hb2 x
    have e : T.apply g1 x - T.apply g2 x = T.apply (fun y => g1 y - g2 y) x := by
      rw [T.apply_eq_integral hlam0, T.apply_eq_integral hlam0, T.apply_eq_integral hlam0]
      simp only
      rw [← integral_sub i1 i2]
      congr 1
      funext η
      ring
    rw [e]
    exact hsup _ M hM hb x
  have hLclose : ∀ η : ℝ, 0 < η →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ V, |L (φ ε) y - g y| ≤ η := fun η hη =>
    eventually_abs_sub_le_of_tendstoUniformlyOn hL hη
  have hvclose : ∀ η : ℝ, 0 < η →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ V, |φ ε y - v y| ≤ η := fun η hη =>
    eventually_abs_sub_le_of_tendstoUniformlyOn hv hη
  -- pointwise convergence of `T (L φ_ε)`
  have hconv : ∀ x ∈ V,
      Tendsto (fun ε => T.apply (L (φ ε)) x) (𝓝[>] (0 : ℝ)) (𝓝 (T.apply g x)) := by
    intro x _
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hη : 0 < δ / (2 * Cs) := by positivity
    filter_upwards [hLclose (δ / (2 * Cs)) hη, hLclose 1 one_pos, hLc] with ε h1 h2 h3
    rw [Real.dist_eq]
    have h2' : ∀ y ∈ V, |L (φ ε) y| ≤ Mg + 1 := fun y hy => by
      have := h2 y hy
      have := hgb y hy
      calc |L (φ ε) y| = |g y + (L (φ ε) y - g y)| := by congr 1; ring
        _ ≤ |g y| + |L (φ ε) y - g y| := abs_add_le _ _
        _ ≤ Mg + 1 := by linarith
    have hk := key x (L (φ ε)) g (h3.aestronglyMeasurable hVm) (hg.aestronglyMeasurable hVm)
      (Mg + 1) Mg (by linarith) hMg0 h2' hgb (δ / (2 * Cs)) hη.le h1
    refine hk.trans_lt ?_
    have : Cs * (δ / (2 * Cs)) = δ / 2 := by field_simp
    rw [this]
    linarith
  -- the eventual bound
  have hB : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      holderENorm C.dl α V (fun x => T.apply (L (φ ε)) x) ≤
        ENNReal.ofReal (ε' * (Mg + η) + c' * (Mv + η)) := by
    intro η hη
    filter_upwards [hφ, hLclose η hη, hvclose η hη] with ε h1 h2 h3
    refine h1.trans ?_
    have s1 := iSup_ofReal_abs_le_add (V := V) (L (φ ε)) g h2
    have s2 := iSup_ofReal_abs_le_add (V := V) (φ ε) v h3
    change (⨆ x : V, ENNReal.ofReal |L (φ ε) x|) ≤ Sg + ENNReal.ofReal η at s1
    change (⨆ x : V, ENNReal.ofReal |φ ε x|) ≤ Sv + ENNReal.ofReal η at s2
    rw [eg] at s1
    rw [ev] at s2
    calc ENNReal.ofReal ε' * (⨆ x : V, ENNReal.ofReal |L (φ ε) x|) +
          ENNReal.ofReal c' * ⨆ x : V, ENNReal.ofReal |φ ε x|
        ≤ ENNReal.ofReal ε' * (ENNReal.ofReal Mg + ENNReal.ofReal η) +
          ENNReal.ofReal c' * (ENNReal.ofReal Mv + ENNReal.ofReal η) :=
          add_le_add (mul_le_mul' le_rfl s1) (mul_le_mul' le_rfl s2)
      _ = ENNReal.ofReal (ε' * (Mg + η) + c' * (Mv + η)) := by
          rw [ENNReal.ofReal_add (mul_nonneg hε'.le (add_nonneg hMg0 hη.le))
            (mul_nonneg hc'.le (add_nonneg hMv0 hη.le)), ENNReal.ofReal_mul hε'.le,
            ENNReal.ofReal_mul hc'.le, ENNReal.ofReal_add hMg0 hη.le,
            ENNReal.ofReal_add hMv0 hη.le]
  -- the limit
  have hfin : ∀ η : ℝ, 0 < η → holderENorm C.dl α V (T.apply g) ≤
      ENNReal.ofReal (2 * (ε' * (Mg + η) + c' * (Mv + η))) := by
    intro η hη
    have hlim := S.holderENorm_limit_le_add_self C.dl hα0 V hsep
      (fun ε x => T.apply (L (φ ε)) x) (T.apply g) hconv
      (ENNReal.ofReal (ε' * (Mg + η) + c' * (Mv + η))) ENNReal.ofReal_lt_top (hB η hη)
    have hP : 0 ≤ ε' * (Mg + η) + c' * (Mv + η) :=
      add_nonneg (mul_nonneg hε'.le (add_nonneg hMg0 hη.le))
        (mul_nonneg hc'.le (add_nonneg hMv0 hη.le))
    refine hlim.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add hP hP]
    congr 1
    ring
  have hfin' : ∀ η : ℝ, 0 < η → holderENorm C.dl α V (T.apply g) ≤
      ENNReal.ofReal (2 * (ε' * Mg + c' * Mv) + (2 * ε' + 2 * c') * η) := fun η hη => by
    refine (hfin η hη).trans (le_of_eq ?_)
    congr 1
    ring
  have hres := le_ofReal_of_forall_pos hfin'
  refine hres.trans (le_of_eq ?_)
  rw [eg, ev, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * ε'),
    ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * c'),
    ← ENNReal.ofReal_add (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * ε') hMg0)
      (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * c') hMv0)]
  congr 1
  ring

end RothschildStein.P2

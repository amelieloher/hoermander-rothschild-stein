-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityTheoremHolder

/-!
# Continuity: the unique bounded `L^p` extension of an operator on the Hölder class

An operator `S` on functions on an open patch `V` of finite measure that is linear on the Hölder
class `{f | ‖f‖_{C^α(V)} < ∞}` and bounded on `L^p` there extends uniquely to a bounded operator on
`L^p(V)` (tests are dense in `L^p(V)`, "localized smooth density", BB pp. 325-326), and the extension
agrees almost everywhere with `S f` on every `f` of finite Hölder norm (the two realizations agree on
the intersection: the extension is bounded, `S` is bounded in `L^p` by the Hölder-class bound, and a
Hölder function is approximated in `L^p` by tests with the difference again of finite Hölder norm).

This is the extension step of the continuity theorem: localized smooth density gives the unique
bounded `L^p` extension (BB pp. 325–326), and approximation together with the bounded adjoint shows
that it agrees almost everywhere with the original operator on the Hölder class.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1

section Extension

variable {N : ℕ}

/-- An operator `S` on functions is **linear and `L^P`-bounded on the Hölder class** of the
open patch `Vo` (for the distance `dl`): tests have finite Hölder norm, `S` is additive, homogeneous
and subtractive on the Hölder class (the homogeneity for those multiples that are again of finite
norm), and for every `0 < α < 1` there is `Λ` with
`‖S f‖_{L^P(Vo)} ≤ Λ ‖f‖_{L^P(Vo)}` for every measurable `f` of finite Hölder norm. -/
structure HolderLpClass (Vo : Opens (Fin N → ℝ))
    (dl : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (S : ((Fin N → ℝ) → ℝ) → ((Fin N → ℝ) → ℝ))
    (P : ℝ≥0∞) : Prop where
  test_holder : ∀ (f : TestFunction Vo ℝ (⊤ : ℕ∞)) {α : ℝ}, 0 < α → α < 1 →
    holderENorm dl α (Vo : Set (Fin N → ℝ)) f ≠ ⊤
  bound : ∀ {α : ℝ}, 0 < α → α < 1 → ∃ Λ : ℝ, 0 < Λ ∧ ∀ f : (Fin N → ℝ) → ℝ,
    holderENorm dl α (Vo : Set (Fin N → ℝ)) f ≠ ⊤ →
      AEStronglyMeasurable f (volume.restrict (Vo : Set (Fin N → ℝ))) →
        MemLp (S f) P (volume.restrict (Vo : Set (Fin N → ℝ))) ∧
        eLpNorm (S f) P (volume.restrict (Vo : Set (Fin N → ℝ))) ≤
          ENNReal.ofReal Λ * eLpNorm f P (volume.restrict (Vo : Set (Fin N → ℝ)))
  add : ∀ {α : ℝ}, 0 < α → α < 1 → ∀ f g : (Fin N → ℝ) → ℝ,
    holderENorm dl α (Vo : Set (Fin N → ℝ)) f ≠ ⊤ → holderENorm dl α (Vo : Set (Fin N → ℝ)) g ≠ ⊤ →
      S (fun x => f x + g x) = fun x => S f x + S g x
  smul : ∀ {α : ℝ}, 0 < α → α < 1 → ∀ (c : ℝ) (f : (Fin N → ℝ) → ℝ),
    holderENorm dl α (Vo : Set (Fin N → ℝ)) f ≠ ⊤ →
      holderENorm dl α (Vo : Set (Fin N → ℝ)) (fun x => c * f x) ≠ ⊤ →
        S (fun x => c * f x) = fun x => c * S f x
  sub : ∀ {α : ℝ}, 0 < α → α < 1 → ∀ f g : (Fin N → ℝ) → ℝ,
    holderENorm dl α (Vo : Set (Fin N → ℝ)) f ≠ ⊤ → holderENorm dl α (Vo : Set (Fin N → ℝ)) g ≠ ⊤ →
      S (fun x => f x - g x) = fun x => S f x - S g x

variable {Vo : Opens (Fin N → ℝ)} {dl : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞}
  {S : ((Fin N → ℝ) → ℝ) → ((Fin N → ℝ) → ℝ)} {P : ℝ≥0∞}

/-- **Agreement of the realizations**: a bounded operator `T` on `L^P(Vo)` that equals `S`
on tests equals `S` almost everywhere on every measurable `f` of finite Hölder norm. The proof
approximates `f` by tests `g` in `L^P(Vo)` and uses the linearity of `S` and its `L^P` bound, applied
to `f - g`. -/
theorem HolderLpClass.agree_of_holder (hS : HolderLpClass Vo dl S P)
    (hfin : volume (Vo : Set (Fin N → ℝ)) < ⊤) [Fact (1 ≤ P)] (hPtop : P ≠ ⊤)
    {T : Lp ℝ P (volume.restrict (Vo : Set (Fin N → ℝ))) →L[ℝ]
      Lp ℝ P (volume.restrict (Vo : Set (Fin N → ℝ)))} {Λ : ℝ} (hΛ : ‖T‖ ≤ Λ)
    (hTtest : ∀ f : TestFunction Vo ℝ (⊤ : ℕ∞), ∀ hmem : MemLp (S f) P
      (volume.restrict (Vo : Set (Fin N → ℝ))),
      T (testToLp Vo hfin P f) = hmem.toLp (S f))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {f : (Fin N → ℝ) → ℝ}
    (hf : holderENorm dl α (Vo : Set (Fin N → ℝ)) f ≠ ⊤)
    (hfm : AEStronglyMeasurable f (volume.restrict (Vo : Set (Fin N → ℝ)))) :
    T ((memLp_of_holderENorm_ne_top Vo.isOpen.measurableSet hfin hf hfm P).toLp f) =ᵐ[volume.restrict
      (Vo : Set (Fin N → ℝ))] S f := by
  classical
  have hP1 : 1 ≤ P := Fact.out
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans hΛ
  obtain ⟨Λα, hΛαpos, hΛα⟩ := hS.bound hα0 hα1
  have hfLp := memLp_of_holderENorm_ne_top Vo.isOpen.measurableSet hfin hf hfm P
  obtain ⟨hfo_mem, -⟩ := hΛα f hf hfm
  have key : ∀ ε' : ℝ, 0 < ε' → ‖T (hfLp.toLp f) - hfo_mem.toLp (S f)‖ ≤ (Λ + Λα) * ε' := by
    intro ε' hε'
    obtain ⟨g, hg⟩ := exists_testFunction_eLpNorm_sub_le Vo hfin hP1 hPtop hfLp hε'
    have hgh : holderENorm dl α (Vo : Set (Fin N → ℝ)) g ≠ ⊤ := hS.test_holder g hα0 hα1
    have hgm : AEStronglyMeasurable g (volume.restrict (Vo : Set (Fin N → ℝ))) :=
      g.continuous.aestronglyMeasurable
    have hum : AEStronglyMeasurable (fun x => f x - g x)
        (volume.restrict (Vo : Set (Fin N → ℝ))) := hfm.sub hgm
    have huh : holderENorm dl α (Vo : Set (Fin N → ℝ)) (fun x => f x - g x) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hgh⟩) (holderENorm_sub_le hα0.le f g)
    obtain ⟨hu_mem, hu_bd⟩ := hΛα _ huh hum
    obtain ⟨hg_out, -⟩ := hΛα g hgh hgm
    have hu_Lp := memLp_of_holderENorm_ne_top Vo.isOpen.measurableSet hfin huh hum P
    have hg_mem := testFunction_memLp Vo hfin g P
    have hsub := hS.sub hα0 hα1 f g hf hgh
    have h1 : hfLp.toLp f = hu_Lp.toLp (fun x => f x - g x) + testToLp Vo hfin P g := by
      show hfLp.toLp f = hu_Lp.toLp (fun x => f x - g x) + hg_mem.toLp g
      rw [← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by simp)
    have h2 : hfo_mem.toLp (S f) = hu_mem.toLp (S (fun x => f x - g x)) + hg_out.toLp (S g) := by
      rw [← MemLp.toLp_add]
      refine MemLp.toLp_congr _ _ (ae_of_all _ fun ξ => ?_)
      have := congrFun hsub ξ
      simp only [Pi.add_apply]
      linarith
    have hTg := hTtest g hg_out
    have hdiff : T (hfLp.toLp f) - hfo_mem.toLp (S f) =
        T (hu_Lp.toLp (fun x => f x - g x)) - hu_mem.toLp (S (fun x => f x - g x)) := by
      rw [h1, h2, map_add, hTg]
      abel
    rw [hdiff]
    have hn1 : ‖hu_Lp.toLp (fun x => f x - g x)‖ ≤ ε' := by
      rw [Lp.norm_toLp]
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
      rwa [ENNReal.toReal_ofReal hε'.le] at this
    have hn2 : ‖hu_mem.toLp (S (fun x => f x - g x))‖ ≤ Λα * ε' := by
      rw [Lp.norm_toLp]
      have hfinu : eLpNorm (fun x => f x - g x) P (volume.restrict (Vo : Set (Fin N → ℝ))) ≠ ⊤ :=
        hu_Lp.eLpNorm_lt_top.ne
      have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinu) hu_bd
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛαpos.le] at h3
      refine h3.trans ?_
      have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
      rw [ENNReal.toReal_ofReal hε'.le] at h4
      exact mul_le_mul_of_nonneg_left h4 hΛαpos.le
    calc ‖T (hu_Lp.toLp (fun x => f x - g x)) - hu_mem.toLp (S (fun x => f x - g x))‖
        ≤ ‖T (hu_Lp.toLp (fun x => f x - g x))‖ +
          ‖hu_mem.toLp (S (fun x => f x - g x))‖ := norm_sub_le _ _
      _ ≤ Λ * ε' + Λα * ε' := by
          refine add_le_add ?_ hn2
          calc ‖T (hu_Lp.toLp (fun x => f x - g x))‖
              ≤ ‖T‖ * ‖hu_Lp.toLp (fun x => f x - g x)‖ := T.le_opNorm _
            _ ≤ Λ * ε' := mul_le_mul hΛ hn1 (norm_nonneg _) hΛ0
      _ = (Λ + Λα) * ε' := by ring
  have hzero : T (hfLp.toLp f) = hfo_mem.toLp (S f) := by
    refine eq_of_forall_dist_le fun ε hε => ?_
    rw [dist_eq_norm]
    have hpos : 0 < Λ + Λα + 1 := by linarith
    refine (key (ε / (Λ + Λα + 1)) (by positivity)).trans ?_
    calc (Λ + Λα) * (ε / (Λ + Λα + 1)) = ε * ((Λ + Λα) / (Λ + Λα + 1)) := by ring
      _ ≤ ε * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hε.le
          rw [div_le_one hpos]
          linarith
      _ = ε := mul_one ε
  rw [hzero]
  exact hfo_mem.coeFn_toLp

/-- **The unique bounded `L^P` extension of an operator on the Hölder class** (abstract
form; BB pp. 325-326, "unique by localized smooth density"). For `1 ≤ P < ∞` there is a bounded
operator `T̄` on `L^P(Vo)`, `‖T̄‖ ≤ Λ`, such that `T̄ f = S f` almost everywhere on every test
`f ∈ C_c^∞(Vo)`, and on every measurable `f` of finite Hölder norm for every `0 < α < 1`; `T̄` is the
unique bounded operator that agrees with `S` on tests. -/
theorem HolderLpClass.exists_extension (hS : HolderLpClass Vo dl S P)
    (hfin : volume (Vo : Set (Fin N → ℝ)) < ⊤) [Fact (1 ≤ P)] (hPtop : P ≠ ⊤) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∃ T : Lp ℝ P (volume.restrict (Vo : Set (Fin N → ℝ))) →L[ℝ]
          Lp ℝ P (volume.restrict (Vo : Set (Fin N → ℝ))),
        ‖T‖ ≤ Λ ∧
        (∀ f : TestFunction Vo ℝ (⊤ : ℕ∞),
          T (testToLp Vo hfin P f) =ᵐ[volume.restrict (Vo : Set (Fin N → ℝ))] S f) ∧
        (∀ {α : ℝ}, 0 < α → α < 1 → ∀ f : (Fin N → ℝ) → ℝ,
          ∀ hf : holderENorm dl α (Vo : Set (Fin N → ℝ)) f ≠ ⊤,
          ∀ hfm : AEStronglyMeasurable f (volume.restrict (Vo : Set (Fin N → ℝ))),
          T ((memLp_of_holderENorm_ne_top Vo.isOpen.measurableSet hfin hf hfm P).toLp f) =ᵐ[volume.restrict
            (Vo : Set (Fin N → ℝ))] S f) ∧
        (∀ T' : Lp ℝ P (volume.restrict (Vo : Set (Fin N → ℝ))) →L[ℝ]
            Lp ℝ P (volume.restrict (Vo : Set (Fin N → ℝ))),
          (∀ f : TestFunction Vo ℝ (⊤ : ℕ∞),
            T' (testToLp Vo hfin P f) = T (testToLp Vo hfin P f)) → T' = T) := by
  classical
  obtain ⟨Λ1, hΛ1pos, hΛ1⟩ := hS.bound (α := 1 / 2) (by norm_num) (by norm_num)
  have htest_h : ∀ f : TestFunction Vo ℝ (⊤ : ℕ∞),
      holderENorm dl (1 / 2) (Vo : Set (Fin N → ℝ)) f ≠ ⊤ := fun f =>
    hS.test_holder f (by norm_num) (by norm_num)
  have hout : ∀ f : TestFunction Vo ℝ (⊤ : ℕ∞),
      MemLp (S f) P (volume.restrict (Vo : Set (Fin N → ℝ))) ∧
      eLpNorm (S f) P (volume.restrict (Vo : Set (Fin N → ℝ))) ≤
        ENNReal.ofReal Λ1 * eLpNorm f P (volume.restrict (Vo : Set (Fin N → ℝ))) := fun f =>
    hΛ1 f (htest_h f) f.continuous.aestronglyMeasurable
  let A : TestFunction Vo ℝ (⊤ : ℕ∞) →ₗ[ℝ] Lp ℝ P (volume.restrict (Vo : Set (Fin N → ℝ))) :=
    { toFun := fun f => (hout f).1.toLp (S f)
      map_add' := fun f g => by
        have h := hS.add (α := 1 / 2) (by norm_num) (by norm_num) f g (htest_h f) (htest_h g)
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (ae_of_all _ fun ξ => congrFun h ξ)
      map_smul' := fun c f => by
        have h := hS.smul (α := 1 / 2) (by norm_num) (by norm_num) c f (htest_h f)
          (htest_h (c • f))
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (ae_of_all _ fun ξ => congrFun h ξ) }
  have hbd : ∀ f : TestFunction Vo ℝ (⊤ : ℕ∞), ‖A f‖ ≤ Λ1 * ‖testToLp Vo hfin P f‖ := by
    intro f
    show ‖(hout f).1.toLp (S f)‖ ≤ Λ1 * ‖(testFunction_memLp Vo hfin f P).toLp f‖
    rw [Lp.norm_toLp, Lp.norm_toLp]
    have hfinf : eLpNorm f P (volume.restrict (Vo : Set (Fin N → ℝ))) ≠ ⊤ :=
      (testFunction_memLp Vo hfin f P).eLpNorm_lt_top.ne
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinf) (hout f).2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hΛ1pos.le] at h
  have hdense : DenseRange (testToLp Vo hfin P) := denseRange_testToLp Vo hfin hPtop
  have hTe : ∀ f : TestFunction Vo ℝ (⊤ : ℕ∞),
      A.extendOfNorm (testToLp Vo hfin P) (testToLp Vo hfin P f) = A f := fun f =>
    LinearMap.extendOfNorm_eq hdense ⟨Λ1, hbd⟩ f
  have hnorm := LinearMap.opNorm_extendOfNorm_le hdense hΛ1pos.le hbd
  refine ⟨Λ1, hΛ1pos.le, A.extendOfNorm (testToLp Vo hfin P), hnorm, ?_, ?_, ?_⟩
  · intro f
    rw [hTe f]
    exact (hout f).1.coeFn_toLp
  · intro α hα0 hα1 f hf hfm
    exact hS.agree_of_holder hfin hPtop hnorm (fun f _ => hTe f) hα0 hα1 hf hfm
  · intro T' hT'
    refine (LinearMap.extendOfNorm_unique hdense Λ1 hbd T' ?_).symm
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hT' f, hTe f]

end Extension

end RothschildStein.P1

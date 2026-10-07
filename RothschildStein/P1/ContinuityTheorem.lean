-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityTheoremKernel
public import RothschildStein.P1.ContinuityTheoremExtension

/-!
# Continuity of every type-`λ` operator (`λ ≥ 0`) on a standard frame

For a type-`λ` operator `T` of a kernel frame which is the standard frame of a lifted chart
(`LiftedChart.IsStandardFrame`, with H1's kernel `Γ` and its reflection `Γ*`):

* **`L^p` bound**: for `1 < p < ∞` the action of `T` on tests (the `ρ`-principal value at type `0`, existing
  at every point, plus the multiplier term; the absolutely convergent integral at positive type) is
  bounded, `‖T f‖_p ≤ C ‖f‖_p`, and has a unique bounded extension to `L^p(V)`
  (`TypeOperator.exists_lpExtension_standard`);
* **Hölder bound**: for `0 < α < 1` the pointwise integral/PV on `C^α(V)` satisfies
  `‖T f‖_{C^α(V)} ≤ C ‖f‖_{C^α(V)}` (`TypeOperator.exists_holderENorm_bound_standard`);
* the two realizations agree on the intersection (the last conjunct of the extension theorem).

The proof assembles the principal terms and the regular remainder of a decomposition of budget
`m ≥ 1`
(`TypeOperator.pvBounds`): degree-2 principal terms (singular: near part by H2 on the doubled balls of
the finite localization, regular far part), terms of degree `≤ 1` and the regular remainder
(positive: Schur and `C^α`), with the linearity of the principal value; the multiplier `μ f` is bounded
on `L^p` and `[μ f]_α ≤ ‖μ‖_∞ [f]_α + [μ]_α ‖f‖_∞`. The `L^p` assertion is bounded extension, not
pointwise PV existence for every `L^p` argument. (BB pp. 566–576, Thm 11.29.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1

/-- An exponent `1 < P < ∞` of `ℝ≥0∞` is `ofReal p` with `1 < p`. -/
theorem exists_ofReal_of_one_lt {P : ℝ≥0∞} (hP1 : 1 < P) (hP : P ≠ ⊤) :
    ∃ p : ℝ, 1 < p ∧ P = ENNReal.ofReal p := by
  refine ⟨P.toReal, ?_, (ENNReal.ofReal_toReal hP).symm⟩
  have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hP).mpr hP1
  simpa using this

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The cutoff region of a lifted frame lies in the chart domain. -/
theorem IsLiftedFrame.subset_U (hF : C.IsLiftedFrame F) : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
  subset_closure.trans hF.closure_subset

/-- The cutoff region of a lifted frame has finite measure. -/
theorem IsLiftedFrame.volume_lt_top (hF : C.IsLiftedFrame F) :
    volume (F.V : Set (Fin (n + m) → ℝ)) < ⊤ :=
  lt_of_le_of_lt (measure_mono (hF.subset_U.trans subset_closure))
    C.isCompact_closure_U.measure_lt_top

/-- The principal value exists at every point for `f` of finite Hölder norm. -/
theorem PVBounds.hasRhoPV {ν : (Fin (n + m) → ℝ) → ℝ} {V : Set (Fin (n + m) → ℝ)}
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (h : C.PVBounds ν V κ) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {f : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α V f ≠ ⊤)
    (ξ : Fin (n + m) → ℝ) :
    HasRhoPV (C.rhoGauge ν) κ f ξ (rhoPV (C.rhoGauge ν) κ f ξ) := by
  obtain ⟨CH, -, hb⟩ := h.holder hα0 hα1
  exact (hb f hf).1 ξ

variable {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ}

/-- **The action of a type-`λ` operator on `C^α(V)`**: for `f` of finite Hölder norm every
`ρ`-truncation is integrable and the operator has a value at every point
(`TypeOperator.HasValue`), and the action is the `ρ`-principal value of the kernel plus the
multiplier term `μ f` (at positive type `μ = 0` and the principal value is the absolutely convergent
integral). -/
theorem _root_.RothschildStein.P1.TypeOperator.apply_eq_rhoPV_add
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤) :
    (∀ ξ, T.HasValue f ξ (T.apply f ξ)) ∧
      T.apply f = fun ξ => rhoPV (C.rhoGauge H.norm) T.kernel f ξ + T.mult ξ * f ξ := by
  have hpv := (T.pvBounds hF).hasRhoPV hα0 hα1 hf
  have hrho : F.rho = C.rhoGauge H.norm :=
    kernelFrame_rho_eq_rhoGauge hF.lifted.Θ_eq hF.gauge_eq
  have happ : T.apply f = fun ξ => rhoPV (C.rhoGauge H.norm) T.kernel f ξ + T.mult ξ * f ξ := by
    funext ξ
    by_cases hlam : lam = 0
    · subst hlam
      rw [typeOperator_apply_eq_rhoPV, hrho]
    · have hmult : T.mult ξ = 0 := by
        have := congrFun (T.mult_eq_zero hlam) ξ
        simpa using this
      have hpatch := TypeOperator.patchKernel hF.lifted (Nat.one_le_iff_ne_zero.mpr hlam) T
      have hfm : AEStronglyMeasurable f (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
        aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U F.V.isOpen.measurableSet hα0
          (lt_top_iff_ne_top.mpr hf)
      have hint := hasRhoPV_of_patchKernel H.norm.gauge hpatch hfm ENNReal.toReal_nonneg
        (fun y hy => abs_le_toReal_holderENorm hf hy) ξ
      rw [T.apply_eq_integral hlam, hmult, zero_mul, add_zero]
      exact hint.rhoPV_eq.symm
  refine ⟨fun ξ => ?_, happ⟩
  rw [hasValue_iff_hasRhoPV, hrho, happ]
  simpa using hpv ξ

/-- The action of a type-`λ` operator is additive on the Hölder class (the principal values
exist at every point, so they add). -/
theorem _root_.RothschildStein.P1.TypeOperator.apply_add_of_holder
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {f g : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤)
    (hg : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤) :
    T.apply (fun x => f x + g x) = (fun ξ => T.apply f ξ + T.apply g ξ) := by
  have hB := T.pvBounds hF
  have hfg : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => f x + g x) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (holderENorm_add_le hα0.le f g)
  funext ξ
  rw [congrFun (T.apply_eq_rhoPV_add hF hα0 hα1 hfg).2 ξ,
    congrFun (T.apply_eq_rhoPV_add hF hα0 hα1 hf).2 ξ,
    congrFun (T.apply_eq_rhoPV_add hF hα0 hα1 hg).2 ξ,
    ((hB.hasRhoPV hα0 hα1 hf ξ).add (hB.hasRhoPV hα0 hα1 hg ξ)).rhoPV_eq]
  ring

/-- The action of a type-`λ` operator is subtractive on the Hölder class. -/
theorem _root_.RothschildStein.P1.TypeOperator.apply_sub_of_holder
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {f g : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤)
    (hg : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤) :
    T.apply (fun x => f x - g x) = (fun ξ => T.apply f ξ - T.apply g ξ) := by
  have hB := T.pvBounds hF
  have hfg : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => f x - g x) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (holderENorm_sub_le hα0.le f g)
  funext ξ
  rw [congrFun (T.apply_eq_rhoPV_add hF hα0 hα1 hfg).2 ξ,
    congrFun (T.apply_eq_rhoPV_add hF hα0 hα1 hf).2 ξ,
    congrFun (T.apply_eq_rhoPV_add hF hα0 hα1 hg).2 ξ,
    ((hB.hasRhoPV hα0 hα1 hf ξ).sub (hB.hasRhoPV hα0 hα1 hg ξ)).rhoPV_eq]
  ring

/-- The action of a type-`λ` operator is homogeneous on the Hölder class. -/
theorem _root_.RothschildStein.P1.TypeOperator.apply_const_mul_of_holder
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤)
    (c : ℝ) (hcf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => c * f x) ≠ ⊤) :
    T.apply (fun x => c * f x) = (fun ξ => c * T.apply f ξ) := by
  have hB := T.pvBounds hF
  funext ξ
  rw [congrFun (T.apply_eq_rhoPV_add hF hα0 hα1 hcf).2 ξ,
    congrFun (T.apply_eq_rhoPV_add hF hα0 hα1 hf).2 ξ,
    ((hB.hasRhoPV hα0 hα1 hf ξ).const_mul c).rhoPV_eq]
  ring

/-- **The Hölder-class data of a type-`λ` operator** for `L^P`, `1 < P < ∞`: tests have finite
Hölder norm, the action is linear on the Hölder class, and it is bounded in `L^P` there (the principal
value by `PVBounds.lp`, the multiplier term by the sup bound of `μ`). -/
theorem _root_.RothschildStein.P1.TypeOperator.holderLpClass (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) {P : ℝ≥0∞} (hP1 : 1 < P) (hP : P ≠ ⊤) :
    HolderLpClass F.V C.dl T.apply P := by
  obtain ⟨p, hp, rfl⟩ := exists_ofReal_of_one_lt hP1 hP
  have hB := T.pvBounds hF
  refine ⟨fun f {α} hα0 hα1 => holderENorm_ne_top_of_contDiff_compact hF.lifted.subset_U f.contDiff
      f.hasCompactSupport (f.tsupport_subset.trans hF.lifted.subset_U) hα0 hα1.le,
    fun {α} hα0 hα1 => ?_, fun {α} hα0 hα1 f g hf hg => T.apply_add_of_holder hF hα0 hα1 hf hg,
    fun {α} hα0 hα1 c f hf hcf => T.apply_const_mul_of_holder hF hα0 hα1 hf c hcf,
    fun {α} hα0 hα1 f g hf hg => T.apply_sub_of_holder hF hα0 hα1 hf hg⟩
  obtain ⟨Λ₁, hΛ₁, hb⟩ := hB.lp hp hα0 hα1
  obtain ⟨M, hM⟩ := T.mult.continuous.bounded_above_of_compact_support T.mult.hasCompactSupport
  have hM' : ∀ x, |T.mult x| ≤ M := fun x => by simpa using hM x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  refine ⟨Λ₁ + M, by positivity, fun f hf hfm => ?_⟩
  have hfLp := memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hF.lifted.volume_lt_top hf
    hfm (ENNReal.ofReal p)
  obtain ⟨hm₁, hn₁⟩ := hb f hf hfm
  obtain ⟨hm₂, hn₂⟩ := memLp_mul_of_bound (b := fun x => T.mult x) (M := M)
    T.mult.continuous.aestronglyMeasurable hM' hfLp
  rw [(T.apply_eq_rhoPV_add hF hα0 hα1 hf).2]
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  refine ⟨hm₁.add hm₂, ?_⟩
  calc eLpNorm (fun ξ => rhoPV (C.rhoGauge H.norm) T.kernel f ξ + T.mult ξ * f ξ)
        (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
      ≤ eLpNorm (rhoPV (C.rhoGauge H.norm) T.kernel f) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
        eLpNorm (fun ξ => T.mult ξ * f ξ) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := eLpNorm_add_le hp1
    _ ≤ ENNReal.ofReal Λ₁ * eLpNorm f (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
        ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := add_le_add hn₁ hn₂
    _ = ENNReal.ofReal (Λ₁ + M) * eLpNorm f (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
        rw [ENNReal.ofReal_add hΛ₁.le hM0, add_mul]

/-- **Hölder bound for every type-`λ` operator on a standard frame** (BB pp. 566–576, Thm 11.29): for
`0 < α < 1` there is `C_H` with `‖T f‖_{C^α(V)} ≤ C_H ‖f‖_{C^α(V)}` (`holderENorm`, lifted
control distance). For `f` of finite Hölder norm the operator has a value at every point
(`TypeOperator.HasValue`: integrable truncations; the `ρ`-principal value at type `0`). -/
theorem _root_.RothschildStein.P1.TypeOperator.exists_holderENorm_bound_standard
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧
      (∀ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤ →
        ∀ ξ, T.HasValue f ξ (T.apply f ξ)) ∧
      ∀ f : (Fin (n + m) → ℝ) → ℝ,
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (T.apply f) ≤
          ENNReal.ofReal CH * holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f := by
  obtain ⟨CH₁, hCH₁, hb⟩ := (T.pvBounds hF).holder hα0 hα1
  obtain ⟨Kμ, hKμ, hKb⟩ := LiftedChart.exists_holderENorm_mul_le (C := C) F.V.isOpen
    hF.lifted.subset_U T.mult.contDiff T.mult.hasCompactSupport T.mult.tsupport_subset hα0 hα1.le
  refine ⟨CH₁ + Kμ, by positivity, fun f hf ξ => (T.apply_eq_rhoPV_add hF hα0 hα1 hf).1 ξ,
    fun f => ?_⟩
  by_cases hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f = ⊤
  · rw [hf, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    exact le_top
  · rw [(T.apply_eq_rhoPV_add hF hα0 hα1 hf).2]
    calc holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
          (fun ξ => rhoPV (C.rhoGauge H.norm) T.kernel f ξ + T.mult ξ * f ξ)
        ≤ holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
            (rhoPV (C.rhoGauge H.norm) T.kernel f) +
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun ξ => T.mult ξ * f ξ) :=
          holderENorm_add_le hα0.le _ _
      _ ≤ ENNReal.ofReal CH₁ * holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f +
          ENNReal.ofReal Kμ * holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f :=
          add_le_add ((hb f hf).2) (hKb f)
      _ = ENNReal.ofReal (CH₁ + Kμ) * holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f := by
          rw [ENNReal.ofReal_add hCH₁.le hKμ.le, add_mul]

/-- **The `L^p` bound on the Hölder class and on tests**: for `1 < P < ∞` there is `Λ` with
`‖T f‖_{L^P(V)} ≤ Λ ‖f‖_{L^P(V)}` for every test function `f ∈ C_c^∞(V)` (the action, as a principal value at
every point), and `T f ∈ L^P(V)`. -/
theorem _root_.RothschildStein.P1.TypeOperator.exists_lp_bound_standard
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {P : ℝ≥0∞} (hP1 : 1 < P)
    (hP : P ≠ ⊤) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
      MemLp (T.apply f) P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ∧
      eLpNorm (T.apply f) P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
        ENNReal.ofReal Λ * eLpNorm f P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  have hS := T.holderLpClass hF hP1 hP
  obtain ⟨Λ, hΛ, hb⟩ := hS.bound (α := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨Λ, hΛ, fun f => hb f (hS.test_holder f (by norm_num) (by norm_num))
    f.continuous.aestronglyMeasurable⟩

/-- **`L^p` bound for every type-`λ` operator on a standard frame**: for `1 < P < ∞` the action on
tests (existing at every point, `HasValue`) has a unique bounded extension `T̄` to `L^P(V)`,
`‖T̄ f‖_P ≤ Λ ‖f‖_P`; it agrees almost everywhere with the pointwise integral/PV on every measurable
`f` of finite Hölder norm (**the two realizations agree on the intersection**), and is the only
bounded operator on `L^P(V)` that agrees with `T` on tests (BB pp. 325–326, 566–576). -/
theorem _root_.RothschildStein.P1.TypeOperator.exists_lpExtension_standard
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) {P : ℝ≥0∞} [Fact (1 ≤ P)]
    (hP1 : 1 < P) (hP : P ≠ ⊤) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∃ Tb : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →L[ℝ]
          Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
        ‖Tb‖ ≤ Λ ∧
        (∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), (∀ ξ, T.HasValue f ξ (T.apply f ξ)) ∧
          Tb (testToLp F.V hF.lifted.volume_lt_top P f) =ᵐ[volume.restrict
            (F.V : Set (Fin (n + m) → ℝ))] T.apply f) ∧
        (∀ {α : ℝ}, 0 < α → α < 1 → ∀ f : (Fin (n + m) → ℝ) → ℝ,
          ∀ hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤,
          ∀ hfm : AEStronglyMeasurable f (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
          Tb ((memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hF.lifted.volume_lt_top hf hfm
              P).toLp f) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] T.apply f) ∧
        (∀ T' : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →L[ℝ]
            Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
          (∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
            T' (testToLp F.V hF.lifted.volume_lt_top P f) =
              Tb (testToLp F.V hF.lifted.volume_lt_top P f)) → T' = Tb) := by
  have hS := T.holderLpClass hF hP1 hP
  obtain ⟨Λ, hΛ, Tb, hn, ht, hh, hu⟩ := hS.exists_extension hF.lifted.volume_lt_top hP
  refine ⟨Λ, hΛ, Tb, hn, fun f => ⟨?_, ht f⟩, hh, hu⟩
  exact (T.apply_eq_rhoPV_add hF (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (hS.test_holder f (by norm_num) (by norm_num))).1

end LiftedChart

end RothschildStein.P1

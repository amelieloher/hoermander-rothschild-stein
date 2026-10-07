-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixSingular
public import RothschildStein.P1.RightParametrixTransport
public import RothschildStein.P2.CutoffsFields
public import RothschildStein.P2.CutoffsHomogeneous
public import RothschildStein.H1.KernelData

/-!
# The right parametrix: weighted bounds for the pole and the remainder fields; first-order integration by parts

The symbol classes of the radial cutoff construction (`RothschildStein.P2.Sym`) give, for a fixed centre `η`, the bounds of
the right pole computation ("`R_{[i]}` has weight `≥ 0` and `R_{[0]}` weight `≥ -1`,
so the error terms have degrees `≤ 1`"):

* an H1 fundamental kernel `Γ` is in every class `Sym (2 - Q)` (homogeneity and smoothness off `0`);
* the coordinates of `Y_i` are in `Sym (ω_j - w_i)` and those of the remainder field `R_{[i],η}`
  in `Sym (ω_j - (w_i - 1))` (vanishing weighted jets, `Sym.of_jets`);
* a field whose coordinates lie in `Sym (ω_j - e)` lowers symbol degrees by `e`
  (`Sym.fieldDeriv`).

`IbpPair W V h` records the first-order identity `∫_W (V h) φ = ∫_W h (Vᵀ φ)` for all tests `φ`
(with integrability of the left side); it holds for smooth `h` (`ibpPair_of_smooth`) and for a
symbol `h` of degree `d` against a field of lowering `e` when `1 - Q ≤ d - e`
(`ibpPair_of_sym`, from the cutoff-shell estimate `integral_fieldDerivative_mul_test_of_shell`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
open RothschildStein.P2
namespace RothschildStein.P1

section Pair

variable {N : ℕ}

/-- The first-order integration by parts identity of a field `V` and a function
`h` over an open set `W`: for every test function `φ` on `W`, `(V h) φ` is integrable and
`∫_W (V h) φ = ∫_W h (Vᵀ φ)`. -/
def IbpPair (W : Opens (Fin N → ℝ)) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (h : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ φ : TestFunction W ℝ (⊤ : ℕ∞),
    IntegrableOn (fun u => fieldDerivative V h u * φ u) (W : Set (Fin N → ℝ)) ∧
    (∫ u in (W : Set (Fin N → ℝ)), fieldDerivative V h u * φ u) =
      ∫ u in (W : Set (Fin N → ℝ)), h u * fieldTranspose V φ u

/-- The identity of `IbpPair` for a smooth field and a smooth function. -/
theorem ibpPair_of_smooth (W : Opens (Fin N → ℝ)) {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {h : (Fin N → ℝ) → ℝ} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (W : Set (Fin N → ℝ)))
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h (W : Set (Fin N → ℝ))) : IbpPair W V h := fun φ =>
  ⟨(S.integrable_mul_test W ((S.contDiffOn_fieldDerivative W V h hV hh).continuousOn.locallyIntegrableOn
      W.isOpen.measurableSet) φ).integrableOn,
    S.integral_fieldDerivative_mul_test W V hV h (hh.of_le (by simp)) φ⟩

end Pair

section Chart

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The coordinates of a model field `Y_i` lie in the symbol class of degree
`ω_j - w_i`. -/
theorem sym_modelField (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (Kc : Set (Fin (n + m) → ℝ)) (ρ : ℝ) (i : Fin k) (j : Fin (n + m)) (kk : ℕ) :
    Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ)) (fun _ u => C.Y i u j) := by
  refine Sym.of_homogeneous C.G (c := chartCtx C ν Kc ρ) rfl ν.gauge kk _ (fun u => C.Y i u j)
    ((contDiff_pi.1 (C.model_field_smooth i) j).contDiffOn) ?_
  intro t ht u _
  have h := congrFun (C.model_field_homogeneous i t ht u) j
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  simp only [HomogeneousGroup.dilate, coordinateDilation]
  rw [sub_eq_add_neg, zpow_add₀ ht.ne', zpow_natCast]
  ring

/-- The coordinates of the remainder field `R_{[i],η}` lie in the symbol class
of degree `ω_j - (w_i - 1)` (`remainder_weight`: the weighted jets vanish below
`1 - w_i + ω_j`, BB pp. 547–548), uniformly for centres in a compact subset of `C.U`. -/
theorem sym_remainderField (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ C.T) (i : Fin k) (j : Fin (n + m))
    (kk : ℕ) :
    Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - (((w i : ℕ) : ℤ) - 1))
      (fun η u => C.R [i] η u j) := by
  have hc := chartCtx_good C ν Kc hρ0 hρ1
  have hjet : ∀ η ∈ Kc, JetVanish C.G.weight (1 - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ))
      (fun u => C.R [i] η u j) := by
    intro η hη
    have h := C.remainder_weight [i] (List.cons_ne_nil i []) η (hKU hη)
    rw [wordWeight_singleton] at h
    exact weightedJet_iff.1 h j
  have h := Sym.of_jets C.G (c := chartCtx C ν Kc ρ) hc rfl ν.gauge hKc C.isOpen_T
    (fun η hη u hu => hT η hη u hu) kk _ (fun z => C.R [i] z.1 z.2 j)
    (contDiffOn_pi.1 (C.remainder_smooth [i]) j) hjet
  exact Sym.mono_d _ hc (le_of_eq (by ring)) h

/-- An H1 fundamental kernel lies in every symbol class of degree `2 - Q`:
it is smooth off the origin and homogeneous of degree `2 - Q`. -/
theorem sym_kernel (C : LiftedChart w st Ω hΩ X x₀ m) {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (K : H1.FundamentalKernel C.G H) (ν : G2.HomogeneousNorm C.G)
    (Kc : Set (Fin (n + m) → ℝ)) (ρ : ℝ) (kk : ℕ) :
    Sym (chartCtx C ν Kc ρ) kk (2 - (C.G.homogeneousDimension : ℤ))
      (fun _ => (K : (Fin (n + m) → ℝ) → ℝ)) := by
  refine Sym.of_homogeneous C.G (c := chartCtx C ν Kc ρ) rfl ν.gauge kk _ _ K.smooth_off_zero ?_
  intro t ht u hu
  rw [K.homogeneous t ht u hu, ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

/-- First-order integration by parts against a symbol: if the coordinates of
`Z η` lie in `Sym (ω_j - e)` (`0 ≤ e`), `A` is a family in every class `Sym d` with
`1 - Q ≤ d - e`, and `Z η₀`, `A η₀` are smooth on the target of `e η₀` (the latter off the origin),
then `∫ (Z A) φ = ∫ A (Zᵀ φ)` for every test `φ` on the target (the shell bound
`|A| |Z ν| ≲ ν^{2-Q}` holds because `Z ν` lies in `Sym (1 - e)`). -/
theorem ibpPair_of_sym (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {η₀ : Fin (n + m) → ℝ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {Z : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)} {e : ℤ} (he : 0 ≤ e)
    (hZ : ∀ (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C ν {η₀} ρ) kk ((C.G.weight j : ℤ) - e) (fun η u => Z η u j))
    (hZs : ContDiffOn ℝ (⊤ : ℕ∞) (Z η₀) (C.e η₀).target)
    {A : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {d : ℤ}
    (hA : ∀ kk : ℕ, Sym (chartCtx C ν {η₀} ρ) kk d A)
    (hd : 1 - (C.G.homogeneousDimension : ℤ) ≤ d - e)
    (hAs : ContDiffOn ℝ (⊤ : ℕ∞) (A η₀) ((C.e η₀).target ∩ {0}ᶜ)) :
    IbpPair (C.modelOpens η₀) (Z η₀) (A η₀) := by
  intro φ
  have hc : (chartCtx C ν {η₀} ρ).Good := chartCtx_good C ν {η₀} hρ0 hρ1
  have hη₀ : η₀ ∈ (chartCtx C ν {η₀} ρ).Kc := mem_singleton _
  set Q : ℤ := (C.G.homogeneousDimension : ℤ) with hQ
  -- shell bound
  have hVν : Sym (chartCtx C ν {η₀} ρ) 0 (1 - e)
      (fun η u => fderiv ℝ (gaugeFamily C ν η) u (Z η u)) :=
    Sym.fieldDeriv (chartCtx C ν {η₀} ρ) hc hZ (gaugeFamily_sym C ν hν {η₀} ρ 1)
  have hprod := Sym.mono_d_zero (chartCtx C ν {η₀} ρ) hc (d' := 2 - Q) (by omega)
    (Sym.mul_zero_part (chartCtx C ν {η₀} ρ) (hA 0) hVν)
  obtain ⟨M, hM⟩ := hprod.bound (chartCtx C ν {η₀} ρ)
  have hshell : ∀ u ∈ ((C.modelOpens η₀ : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)),
      0 < ν u → ν u < ρ → |A η₀ u| * |fieldDerivative (Z η₀) (ν : (Fin (n + m) → ℝ) → ℝ) u| ≤
        M * ν u ^ (2 - Q) := by
    intro u _ hu0 hu1
    have := hM η₀ hη₀ u ⟨hu0, hu1⟩
    rw [← abs_mul]
    exact this
  -- integrability
  have hVh : Sym (chartCtx C ν {η₀} ρ) 0 (d - e) (fun η u => fderiv ℝ (A η) u (Z η u)) :=
    Sym.fieldDeriv (chartCtx C ν {η₀} ρ) hc hZ (hA 1)
  obtain ⟨M₁, hM₁⟩ := hVh.bound (chartCtx C ν {η₀} ρ)
  obtain ⟨M₂, hM₂⟩ := (hA 0).bound (chartCtx C ν {η₀} ρ)
  have hOpen : IsOpen ((C.e η₀).target ∩ {0}ᶜ) := (C.e η₀).open_target.inter isOpen_compl_singleton
  have hZs' : ContDiffOn ℝ (⊤ : ℕ∞) (Z η₀)
      ((C.modelOpens η₀ : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) := hZs
  have hFc : ContinuousOn (fieldDerivative (Z η₀) (A η₀)) ((C.e η₀).target ∩ {0}ᶜ) :=
    (S.contDiffOn_fieldDerivative (⟨(C.e η₀).target ∩ {0}ᶜ, hOpen⟩ : Opens (Fin (n + m) → ℝ))
      (Z η₀) (A η₀) (hZs.mono inter_subset_left) hAs).continuousOn
  have h1 : IntegrableOn (fun u => fieldDerivative (Z η₀) (A η₀) u * φ u)
      ((C.modelOpens η₀ : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) :=
    integrableOn_mul_test_of_gauge_bound ν (C.modelOpens η₀) hFc hρ0 (d := d - e) (by omega)
      (fun u hu0 hu1 => hM₁ η₀ hη₀ u ⟨hu0, hu1⟩) φ
  have h2 : IntegrableOn (fun u => A η₀ u * fieldTranspose (Z η₀) φ u)
      ((C.modelOpens η₀ : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) := by
    have := integrableOn_mul_test_of_gauge_bound ν (C.modelOpens η₀) hAs.continuousOn hρ0
      (d := d) (by omega) (fun u hu0 hu1 => hM₂ η₀ hη₀ u ⟨hu0, hu1⟩)
      (fieldTransposeTest (C.modelOpens η₀) (Z η₀) hZs' φ)
    refine this.congr_fun (fun u _ => ?_) (C.e η₀).open_target.measurableSet
    show A η₀ u * (fieldTransposeTest (C.modelOpens η₀) (Z η₀) hZs' φ) u = _
    rw [S.fieldTransposeTest_apply]
  exact ⟨h1, integral_fieldDerivative_mul_test_of_shell ν hν (C.modelOpens η₀) hZs' hAs φ h1 h2 hρ0 hshell⟩

end Chart

end RothschildStein.P1

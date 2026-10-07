-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderEndpoint
public import RothschildStein.S.SobolevCutoffZero
public import RothschildStein.S.SobolevZeroAE
public import RothschildStein.S.Locality

/-!
# Hölder jets, supports, and the Hölder form of the differentiated endpoint identity

Support lemmas for the Hölder weak jets `LiftedChart.IsHolderWeakJet` of the no-drift chart used by
the compact recurrence and the regularity induction of the higher Hölder estimate:

* `holderJetNorm`: the weighted Hölder norm `∑_{|K| ≤ N} ‖D K‖_{C^α(V)}` of a jet;
* a Hölder weak jet is an `L^2` weak jet (`isWeakJet_of_holder`);
* the entries of the jet of a function vanishing on `V \ K₀` vanish pointwise there
  (`jet_vanish_off`), and an `L^2` function vanishing off a compact subset of `V` lies in
  `W_{X̃,0}(V)` (`memSobolevXZero_of_zero_off`);
* the entry `D K` of a Hölder jet of order `N + 1` is in `W^{1,2}_{X̃,0}(V)` with the shifted jet
  (`jetEntry_sobolev`);
* `endpointDiff_holder`: the Hölder form of `endpointDiff_lp`, with continuity and a norm bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

section Norms

variable {n' k : ℕ}

/-- The weighted Hölder norm of a jet: `∑_{|K| ≤ N} ‖D K‖_{C^α(V)}`. -/
def holderJetNorm (w : Fin k → ℕ+) (d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞) (V : Set (Fin n' → ℝ))
    (α : ℝ) (N : ℕ) (D : List (Fin k) → (Fin n' → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ K ∈ wordFamily w N, holderENorm d α V (D K)

/-- The Hölder norm of a finite sum is at most the sum of the norms. -/
theorem holderENorm_sum_le {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α)
    {V : Set (Fin n' → ℝ)} {ι : Type*} (s : Finset ι) (f : ι → (Fin n' → ℝ) → ℝ) :
    holderENorm d α V (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, holderENorm d α V (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun x => ∑ i ∈ (∅ : Finset ι), f i x) = fun _ => (0 : ℝ) := by
      funext x
      simp
    rw [this, holderENorm_zero]
    simp
  | insert a s ha ih =>
    have e : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x
      rw [Finset.sum_insert ha]
    rw [e, Finset.sum_insert ha]
    exact (holderENorm_add_le hα _ _).trans (add_le_add le_rfl ih)

end Norms

section Jets

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- A Hölder weak jet is an `L^2` weak jet (finite Hölder norm on the finite-volume patch). -/
theorem isWeakJet_of_holder (hF : C.IsLiftedFrame F) {α : ℝ} (hα0 : 0 < α) {kk : ℕ}
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V kk α u D) :
    IsWeakJet w C.Xl F.V kk 2 u D := fun K hK =>
  ⟨(hD K hK).1, memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hF.volume_lt_top (hD K hK).2
    (LiftedChart.aestronglyMeasurable_of_holderENorm_lt_top hF.subset_U F.V.isOpen.measurableSet hα0
      (lt_top_iff_ne_top.2 (hD K hK).2)) 2⟩

/-- The entries of the jet of a function vanishing on `V \ K₀` vanish pointwise on `V \ K₀`
(locality of weak derivatives and continuity of the Hölder entries). -/
theorem jet_vanish_off (hF : C.IsLiftedFrame F) {α : ℝ} (hα0 : 0 < α) {kk : ℕ}
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V kk α u D) {K₀ : Set (Fin (n + m) → ℝ)}
    (hK₀ : IsClosed K₀) (hz : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ K₀ → u x = 0)
    {K : List (Fin k)} (hK : K ∈ wordFamily w kk) :
    ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ K₀ → D K x = 0 := by
  let U : Opens (Fin (n + m) → ℝ) := ⟨(F.V : Set (Fin (n + m) → ℝ)) ∩ K₀ᶜ, F.V.isOpen.inter hK₀.isOpen_compl⟩
  have hUV : (U : Set (Fin (n + m) → ℝ)) ⊆ (F.V : Set (Fin (n + m) → ℝ)) := inter_subset_left
  have hu0 : u =ᵐ[volume.restrict (U : Set (Fin (n + m) → ℝ))] (fun _ => 0) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' U.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hz x hx.1 hx.2
  have hg0 := S.hasWeakWordDeriv_locality C.Xl F.V U hUV (hD K hK).1 hu0
  have hcont : ContinuousOn (D K) (U : Set (Fin (n + m) → ℝ)) :=
    (LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0
      (lt_top_iff_ne_top.2 (hD K hK).2)).mono hUV
  have := Measure.eqOn_open_of_ae_eq hg0 U.isOpen hcont continuousOn_const
  intro x hx hxK
  exact this ⟨hx, hxK⟩

/-- A function of `W^{kk,2}_{X̃}(V)` vanishing on `V \ K₀`, `K₀ ⊆ V` compact, lies in the closure
`W^{kk,2}_{X̃,0}(V)` of the tests (multiplication by a plateau test function). -/
theorem memSobolevXZero_of_zero_off (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)))
    {K₀ : Set (Fin (n + m) → ℝ)} (hK₀ : IsCompact K₀) (hKV : K₀ ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    {kk : ℕ} {h : (Fin (n + m) → ℝ) → ℝ} (hh : memSobolevX w C.Xl F.V kk 2 h)
    (hz : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ K₀ → h x = 0) :
    memSobolevXZero w C.Xl F.V kk 2 h := by
  obtain ⟨χ, U, -, hKU, -, hχ⟩ := S.exists_test_plateau F.V ⟨K₀, hK₀⟩ hKV
  have hmul := S.memSobolevXZero_mul_test w C.Xl F.V hXt kk (p := 2) (by simp) hh χ
  have hae : (fun x => h x * χ x) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] h := by
    rw [Filter.EventuallyEq, ae_restrict_iff' F.V.isOpen.measurableSet]
    refine Filter.Eventually.of_forall fun x hx => ?_
    by_cases hxK : x ∈ K₀
    · have := hχ (hKU hxK)
      simp only [Pi.one_apply] at this
      rw [this, mul_one]
    · rw [hz x hx hxK, zero_mul]
  exact (S.memSobolevXZero_congr_ae C.Xl F.V w kk 2 hae).1 hmul

variable {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **A jet entry is a `W^{1,2}_{X̃,0}` function with the shifted jet.** If `D` is a Hölder weak jet
of order `N + 1` of `u`, `u` vanishes on `V \ K₀` (`K₀ ⊆ V` compact) and `|K| ≤ N`, then `D K ∈
W^{1,2}_{X̃,0}(V)` with weak jet `K' ↦ D (K' ++ K)`. -/
theorem jetEntry_sobolev (hF : C.IsLiftedFrame F) (hw : ∀ j, (w j : ℕ) = 1) {α : ℝ} (hα0 : 0 < α)
    {N : ℕ} {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V (N + 1) α u D) {K₀ : Set (Fin (n + m) → ℝ)}
    (hK₀ : IsCompact K₀) (hKV : K₀ ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (hz : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ K₀ → u x = 0) {K : List (Fin k)}
    (hK : K ∈ wordFamily w N) :
    memSobolevXZero w C.Xl F.V 1 2 (D K) ∧
      IsWeakJet w C.Xl F.V 1 2 (D K) (fun K' => D (K' ++ K)) := by
  have hXt := hF.contDiffOn_Xl
  have hD2 := isWeakJet_of_holder hF hα0 hD
  have hKw : K.length ≤ N := by
    have := (S.mem_wordFamily_iff w N K).1 hK
    rwa [wordWeight_eq_length hw] at this
  have hmem : ∀ K' ∈ wordFamily w 1, K' ++ K ∈ wordFamily w (N + 1) := fun K' hK' => by
    have h1 := (S.mem_wordFamily_iff w 1 K').1 hK'
    rw [wordWeight_eq_length hw] at h1
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
    simp only [List.length_append]
    omega
  have hjet : IsWeakJet w C.Xl F.V 1 2 (D K) (fun K' => D (K' ++ K)) := fun K' hK' =>
    ⟨hD2.hasWeakWordDeriv_append hXt K K' (hmem K' hK'), (hD2 (K' ++ K) (hmem K' hK')).2⟩
  refine ⟨?_, hjet⟩
  have hKmem : K ∈ wordFamily w (N + 1) := by
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]; omega
  refine memSobolevXZero_of_zero_off hXt hK₀ hKV ⟨(hD2 K hKmem).2, fun K' hK' => ?_⟩
    (jet_vanish_off hF hα0 hD hK₀.isClosed hz hKmem)
  exact ⟨D (K' ++ K), (hjet K' hK').1, (hjet K' hK').2⟩

end Jets


section EndpointHolder

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The Hölder form of `endpointDiff_lp`.** For an endpoint operator `Sop`
and a generator `i` there are type-0 operators `Q t l`, `Q0 t` and a constant `Λ` such that, for every
`h ∈ W^{1,2}_{X̃,0}(V)` with weak jet `D h` of finite Hölder norms (`h` and `D h [l]`), the pointwise
action `Sop h` has the weak `X̃_i`-derivative `∑ₜ (∑_l Q_{t l} (D h [l]) + Q_{t 0} h)` (pointwise actions),
which is continuous on `V` with `‖·‖_{C^α(V)} ≤ Λ (‖h‖_{C^α(V)} + ∑_l ‖D h [l]‖_{C^α(V)})` (the continuity theorem). -/
theorem endpointDiff_holder (hF : C.IsStandardFrame F H K hQ) (hw : ∀ j, (w j : ℕ) = 1)
    (hLeftDiff : LeftDifferentiation F w C.Xl) (hcomm : RepComm F C.Xl) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Sop : TypeOperator F 0} (hS : IsEndpoint F C.Xl Sop) (i : Fin k) :
    ∃ (r' : ℕ) (Q : Fin r' → Fin k → TypeOperator F 0) (Q0 : Fin r' → TypeOperator F 0) (Λ : ℝ),
      0 < Λ ∧ ∀ (h : (Fin (n + m) → ℝ) → ℝ) (Dh : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 1 2 h → IsWeakJet w C.Xl F.V 1 2 h Dh →
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) h ≠ ⊤ →
        (∀ l, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (Dh [l]) ≠ ⊤) →
        hasWeakWordDeriv C.Xl F.V [i] (Sop.apply h)
            (fun ξ => ∑ t, ((∑ l, (Q t l).apply (Dh [l]) ξ) + (Q0 t).apply h ξ)) ∧
          ContinuousOn (fun ξ => ∑ t, ((∑ l, (Q t l).apply (Dh [l]) ξ) + (Q0 t).apply h ξ))
            (F.V : Set (Fin (n + m) → ℝ)) ∧
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
              (fun ξ => ∑ t, ((∑ l, (Q t l).apply (Dh [l]) ξ) + (Q0 t).apply h ξ)) ≤
            ENNReal.ofReal Λ * (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) h +
              ∑ l, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (Dh [l])) := by
  classical
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨r', Q, Q0, hlp⟩ := endpointDiff_lp hF hw hLeftDiff hcomm hS i
  choose CQ hCQ hbQ using fun (t : Fin r') (l : Fin k) =>
    (Q t l).exists_holderENorm_bound_standard hF hα0 hα1
  choose CQ0 hCQ0 hbQ0 using fun t : Fin r' => (Q0 t).exists_holderENorm_bound_standard hF hα0 hα1
  have hbQ' : ∀ t l (f : (Fin (n + m) → ℝ) → ℝ), holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      ((Q t l).apply f) ≤ ENNReal.ofReal (CQ t l) *
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f := fun t l f => (hbQ t l).2 f
  have hbQ0' : ∀ t (f : (Fin (n + m) → ℝ) → ℝ), holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      ((Q0 t).apply f) ≤ ENNReal.ofReal (CQ0 t) *
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f := fun t f => (hbQ0 t).2 f
  refine ⟨r', Q, Q0, 1 + ∑ t, ((∑ l, CQ t l) + CQ0 t), ?_, fun h Dh hh hD hh1 hDh1 => ?_⟩
  · have : 0 ≤ ∑ t : Fin r', ((∑ l, CQ t l) + CQ0 t) :=
      Finset.sum_nonneg fun t _ => add_nonneg (Finset.sum_nonneg fun l _ => (hCQ t l).le) (hCQ0 t).le
    linarith
  have hmeas : ∀ {g : (Fin (n + m) → ℝ) → ℝ},
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤ →
      AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := fun hg =>
    LiftedChart.aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U F.V.isOpen.measurableSet
      hα0 (lt_top_iff_ne_top.2 hg)
  have hlp' := hlp h Dh hh hD
  have e0 := Sop.lpAct_holder hF hP1 hP hα0 hα1 hh1 (hmeas hh1)
  have e1 : ∀ t : Fin r', (fun ξ => (∑ l, (Q t l).lpAct hF hP1 hP (Dh [l]) ξ) +
      (Q0 t).lpAct hF hP1 hP h ξ) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
      (fun ξ => (∑ l, (Q t l).apply (Dh [l]) ξ) + (Q0 t).apply h ξ) := fun t => by
    have a1 := ae_eq_finset_sum (μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ))) Finset.univ
      (f := fun l ξ => (Q t l).lpAct hF hP1 hP (Dh [l]) ξ) (g := fun l ξ => (Q t l).apply (Dh [l]) ξ)
      fun l _ => (Q t l).lpAct_holder hF hP1 hP hα0 hα1 (hDh1 l) (hmeas (hDh1 l))
    have a2 := (Q0 t).lpAct_holder hF hP1 hP hα0 hα1 hh1 (hmeas hh1)
    filter_upwards [a1, a2] with ξ b1 b2
    rw [b1, b2]
  have e2 := ae_eq_finset_sum (μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ))) Finset.univ
    (f := fun t ξ => (∑ l, (Q t l).lpAct hF hP1 hP (Dh [l]) ξ) + (Q0 t).lpAct hF hP1 hP h ξ)
    (g := fun t ξ => (∑ l, (Q t l).apply (Dh [l]) ξ) + (Q0 t).apply h ξ) fun t _ => e1 t
  have hweak := S.hasWeakWordDeriv_congr_ae C.Xl F.V hlp' e0 e2
  have hcont : ContinuousOn (fun ξ => ∑ t, ((∑ l, (Q t l).apply (Dh [l]) ξ) + (Q0 t).apply h ξ))
      (F.V : Set (Fin (n + m) → ℝ)) :=
    continuousOn_finsetSum _ fun t _ =>
      (continuousOn_finsetSum _ fun l _ =>
        (Q t l).continuousOn_apply_holder hF hα0 hα1 (hDh1 l)).add
        ((Q0 t).continuousOn_apply_holder hF hα0 hα1 hh1)
  refine ⟨hweak, hcont, ?_⟩
  set N : ℝ≥0∞ := holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) h +
    ∑ l, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (Dh [l]) with hN
  have hh_le : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) h ≤ N := le_self_add
  have hDh_le : ∀ l, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (Dh [l]) ≤ N := fun l =>
    (Finset.single_le_sum (f := fun l => holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (Dh [l]))
      (fun _ _ => zero_le) (Finset.mem_univ l)).trans le_add_self
  have hterm : ∀ t : Fin r', holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      (fun ξ => (∑ l, (Q t l).apply (Dh [l]) ξ) + (Q0 t).apply h ξ) ≤
      ENNReal.ofReal ((∑ l, CQ t l) + CQ0 t) * N := fun t => by
    refine (holderENorm_add_le hα0.le _ _).trans ?_
    have h1 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun ξ => ∑ l, (Q t l).apply (Dh [l]) ξ) ≤
        ENNReal.ofReal (∑ l, CQ t l) * N :=
      holderENorm_finsetSum_le_mul hα0.le (fun l => (Q t l).apply (Dh [l])) (fun l => CQ t l)
        Finset.univ (fun l _ => (hCQ t l).le) fun l _ =>
        (hbQ' t l _).trans (mul_le_mul' le_rfl (hDh_le l))
    have h2 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) ((Q0 t).apply h) ≤
        ENNReal.ofReal (CQ0 t) * N := (hbQ0' t h).trans (mul_le_mul' le_rfl hh_le)
    calc _ ≤ ENNReal.ofReal (∑ l, CQ t l) * N + ENNReal.ofReal (CQ0 t) * N := add_le_add h1 h2
      _ = _ := by
        rw [← add_mul, ENNReal.ofReal_add (Finset.sum_nonneg fun l _ => (hCQ t l).le) (hCQ0 t).le]
  have hsum := holderENorm_finsetSum_le_mul hα0.le
    (fun t => fun ξ => (∑ l, (Q t l).apply (Dh [l]) ξ) + (Q0 t).apply h ξ)
    (fun t => (∑ l, CQ t l) + CQ0 t) Finset.univ
    (fun t _ => add_nonneg (Finset.sum_nonneg fun l _ => (hCQ t l).le) (hCQ0 t).le)
    (fun t _ => hterm t)
  refine hsum.trans (mul_le_mul' ?_ le_rfl)
  exact ENNReal.ofReal_le_ofReal (by linarith)

end EndpointHolder

end RothschildStein.P2.HigherHolder

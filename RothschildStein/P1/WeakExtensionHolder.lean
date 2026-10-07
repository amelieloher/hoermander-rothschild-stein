-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionBasic
public import RothschildStein.P1.WeakExtensionHigher
public import RothschildStein.S.CompactIntrinsicHolderSobolev
public import RothschildStein.S.WeakIntrinsicWords

/-!
# Hölder and noncompact inputs: compactly supported intrinsic `C^{m,α}` inputs

Compactly supported `C^{m,α}` functions and their derivatives belong to the weak Sobolev spaces
above; apply the weak identity and identify the continuous representatives (no Hölder norm
density is used). For `u` in the compact intrinsic Hölder class
(`memHolderXCompact w C.Xl C.dl V m α u`, `0 < α < 1`):

* the inclusion `C^{m,α}_{X̃,0} ⊂ W^{m,2}_{X̃,0}` (`memSobolevXZero_of_memHolderXCompact`, with the
  `(HD1)`-`(HD2)` package `S.DistanceGeometry` of the lifted control distance as an explicit hypothesis) gives
  `u ∈ W^{m,2}_{X̃,0}(V)`; BB Prop 2.22 (`memWeakHolderX_of_memHolderX`) gives a weak jet `D` whose entries have
  finite Hölder norm (`exists_holderWeakJet`, `IsHolderWeakJet`);
* the `L^2` identity of `WeakExtensionBasic` / `WeakExtensionHigher` holds; by the continuity theorem the `L^2`
  extensions agree a.e. with the pointwise integral/PV actions on Hölder inputs (`lpAct_holder`), so the
  identities hold weakly **with the pointwise actions** `T.apply` on the Hölder jet, and both sides are
  continuous functions on `V` (Hölder continuity of type operators): this identifies the continuous representatives
  (`eqOn_of_hasWeakWordDeriv_of_continuousOn`);
* `weakExtension_parametrix_left_holder`: `a u = P₂ L̃u + F₂ u` holds **at every point of `V`**;
  `weakExtension_firstOrder_intrinsic`, `weakExtension_drift_intrinsic`: the right-hand side of the first-order
  resp. drift representation is an intrinsic derivative of `a u` (continuous weak derivatives are
  intrinsic).

Throughout `L̃u = D [0] + ∑ᵢ D [i, i]` (resp. `∑ᵢ D [i, i]`) and `X̃ₖu = D [k]` for the Hölder jet `D`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Generic

variable {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)} {V : Opens (Fin N → ℝ)}

/-- **Continuous weak derivatives are unique pointwise**: two
continuous weak `X̃_I`-derivatives of the same function agree at every point of `V`. -/
theorem eqOn_of_hasWeakWordDeriv_of_continuousOn {I : List (Fin k)} {f g₁ g₂ : (Fin N → ℝ) → ℝ}
    (h1 : hasWeakWordDeriv Xt V I f g₁) (h2 : hasWeakWordDeriv Xt V I f g₂)
    (hc1 : ContinuousOn g₁ (V : Set (Fin N → ℝ))) (hc2 : ContinuousOn g₂ (V : Set (Fin N → ℝ))) :
    EqOn g₁ g₂ (V : Set (Fin N → ℝ)) :=
  Measure.eqOn_open_of_ae_eq (S.hasWeakWordDeriv_unique Xt V h1 h2) V.isOpen hc1 hc2

/-- A continuous weak derivative of a continuous function along a
single letter is the intrinsic derivative (BB Prop 2.22 and its converse, in the form of `S.hasIntrinsicDeriv_of_continuous_weak_derivative`). -/
theorem hasIntrinsicWordDeriv_singleton_of_weak
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ))) (i : Fin k)
    {f g : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f (V : Set (Fin N → ℝ)))
    (hg : ContinuousOn g (V : Set (Fin N → ℝ))) (h : hasWeakWordDeriv Xt V [i] f g) :
    hasIntrinsicWordDeriv Xt V [i] f g := by
  classical
  refine S.hasIntrinsicWordDeriv_of_continuous_weak_subwords V Xt hXt [i] f
    (fun J => if J = [] then f else g) (by simp) (fun J hJ => ?_) (fun J hJ => ?_)
  · rcases List.sublist_singleton.1 hJ with rfl | rfl
    · simpa using S.hasWeakWordDeriv_nil Xt V (hf.locallyIntegrableOn V.isOpen.measurableSet)
    · simpa using h
  · rcases List.sublist_singleton.1 hJ with rfl | rfl
    · simpa using hf
    · simpa using hg

/-- A.e. equality passes through finite sums. -/
theorem ae_eq_finset_sum {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) {f g : ι → α → ℝ} (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun x => ∑ i ∈ s, f i x) =ᵐ[μ] fun x => ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall fun x => by simp
  | insert a s ha ih =>
    filter_upwards [h a (Finset.mem_insert_self a s),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)] with x hx hx'
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hx, hx']

end Generic

section HolderNorm

variable {n' : ℕ} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} {V : Set (Fin n' → ℝ)}

/-- Finite sums of functions of finite Hölder norm have finite
Hölder norm. -/
theorem holderENorm_finset_sum_ne_top (hα : 0 ≤ α) {ι : Type*} (s : Finset ι)
    (f : ι → (Fin n' → ℝ) → ℝ) (h : ∀ i ∈ s, holderENorm d α V (f i) ≠ ⊤) :
    holderENorm d α V (fun x => ∑ i ∈ s, f i x) ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun x => ∑ i ∈ (∅ : Finset ι), f i x) = fun _ => (0 : ℝ) := by
      funext x
      simp
    rw [this, holderENorm_zero]
    exact ENNReal.zero_ne_top
  | insert a s ha ih =>
    have e : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x
      rw [Finset.sum_insert ha]
    rw [e]
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨h a (Finset.mem_insert_self a s),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩) (holderENorm_add_le hα _ _)

end HolderNorm

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ}

/-- `D` is a **weak jet with Hölder entries** of `u`: for every word
`K` of weight at most `kk`, `D K` is a weak `X̃_K`-derivative of `u` on `V` of finite Hölder norm
(for the lifted control distance `d`). -/
def IsHolderWeakJet (w : Fin k → ℕ+) (Xt : Fin k → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (d : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ≥0∞) (V : Opens (Fin (n + m) → ℝ)) (kk : ℕ)
    (α : ℝ) (u : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ) : Prop :=
  ∀ K ∈ wordFamily w kk, hasWeakWordDeriv Xt V K u (D K) ∧
    holderENorm d α (V : Set (Fin (n + m) → ℝ)) (D K) ≠ ⊤

/-- **The inclusion `C^{kk,α}_{X̃,0} ⊂ W^{kk,2}_{X̃,0}` and the weak jet**: a compactly supported intrinsic
`C^{kk,α}_{X̃}` function lies in `W^{kk,2}_{X̃,0}(V)` and a Hölder weak jet `D` is a weak jet in the sense
of `IsWeakJet` (`D K ∈ L^2(V)`: Hölder functions are bounded on the finite-volume patch). -/
theorem memSobolevXZero_of_holder (hF : C.IsStandardFrame F H K hQ) (Ω₂ : Opens (Fin (n + m) → ℝ))
    (G : S.DistanceGeometry Ω₂) (hG : G.d = C.dl)
    (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {kk : ℕ} {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderXCompact w C.Xl C.dl F.V kk α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V kk α u D) :
    memSobolevXZero w C.Xl F.V kk 2 u ∧ IsWeakJet w C.Xl F.V kk 2 u D := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hu' : memHolderXCompact w C.Xl G.d F.V kk α u := by
    rw [hG]
    exact hu
  refine ⟨S.memSobolevXZero_of_memHolderXCompact Ω₂ F.V G hV w C.Xl hF.lifted.contDiffOn_Xl kk hα0
    (by simp) hu', fun K hK => ⟨(hD K hK).1, ?_⟩⟩
  exact memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hF.lifted.volume_lt_top (hD K hK).2
    (aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U F.V.isOpen.measurableSet hα0
      (lt_top_iff_ne_top.2 (hD K hK).2)) 2

end LiftedChart

namespace LiftedChart

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- A horizontal word `[k]` has weight one, so lies in every jet of
order two. -/
theorem horizontal_mem_wordFamily (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (k : Fin q) :
    [k.succ] ∈ wordFamily w 2 :=
  (S.mem_wordFamily_iff w 2 _).2 (by simp [wordWeight, hw k])

/-- The weak `L̃ u` of a Hölder weak jet has finite Hölder norm. -/
theorem IsHolderWeakJet.weakSumSquaresWithDrift_ne_top
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) {α : ℝ} (hα0 : 0 < α)
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D) :
    holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquaresWithDrift D) ≠ ⊤ := by
  obtain ⟨h0, hi⟩ := drift_words_mem_wordFamily (w := w) hw0 hw
  have e : weakSumSquaresWithDrift D =
      fun x => D [0] x + ∑ i ∈ (Finset.univ : Finset (Fin q)), D [i.succ, i.succ] x := rfl
  rw [e]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨(hD [0] h0).2,
    holderENorm_finset_sum_ne_top hα0.le _ _ fun i _ => (hD _ (hi i)).2⟩)
    (holderENorm_add_le hα0.le _ _)

/-- **First-order representation, for compactly supported intrinsic `C^{2,α}` inputs.** Let
`X̃_l(a φ) = F_l L̃φ + S_l φ` weakly for tests `φ`. For `u` in the compact intrinsic class
`memHolderXCompact w C.Xl C.dl V 2 α u` (`0 < α < 1`) with Hölder weak jet `D` (BB Prop 2.22,
`exists_holderWeakJet`), `X̃_l(a u) = F_l (L̃u) + S_l u` weakly on `V`, with the pointwise integral/PV
actions of the type operators on the Hölder inputs `L̃u = D [0] + ∑ᵢ D [i, i]` and `u`; the right-hand side is
continuous on `V`. -/
theorem weakExtension_firstOrder_holder (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Fl : Fin q → TypeOperator F 1}
    {Sl : Fin q → TypeOperator F 0}
    (hid : ∀ (l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
        (fun ξ => (Fl l).apply (sumSquaresWithDrift C.Xl u) ξ + (Sl l).apply u ξ))
    (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂) (hG : G.d = C.dl)
    (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderXCompact w C.Xl C.dl F.V 2 α u)
    {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D)
    (l : Fin q) :
    hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
      (fun ξ => (Fl l).apply (weakSumSquaresWithDrift D) ξ + (Sl l).apply u ξ) ∧
    ContinuousOn (fun ξ => (Fl l).apply (weakSumSquaresWithDrift D) ξ + (Sl l).apply u ξ)
      (F.V : Set (Fin (n + m) → ℝ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨hu0, hD0⟩ := memSobolevXZero_of_holder hF Ω₂ G hG hV hα0 hu hD
  have hweak := weakExtension_firstOrder hF hw0 hw hid hP1 hP hu0 hD0 l
  have hLD := hD.weakSumSquaresWithDrift_ne_top hw0 hw hα0
  have hu1 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := ne_top_of_lt hu.1.1
  have hLDm := aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U
    F.V.isOpen.measurableSet hα0 (lt_top_iff_ne_top.2 hLD)
  have hum := aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U
    F.V.isOpen.measurableSet hα0 (lt_top_iff_ne_top.2 hu1)
  have e1 := (Fl l).lpAct_holder hF hP1 hP hα0 hα1 hLD hLDm
  have e2 := (Sl l).lpAct_holder hF hP1 hP hα0 hα1 hu1 hum
  exact ⟨S.hasWeakWordDeriv_congr_ae C.Xl F.V hweak Filter.EventuallyEq.rfl (e1.add e2),
    ((Fl l).continuousOn_apply_holder hF hα0 hα1 hLD).add
      ((Sl l).continuousOn_apply_holder hF hα0 hα1 hu1)⟩

/-- **First-order representation, intrinsic form.** Under the hypotheses of
`weakExtension_firstOrder_holder`, the continuous function `F_l (L̃u) + S_l u` is an *intrinsic* derivative
`X̃_l(a u)` of `a u` on `V` (a continuous weak derivative of a continuous function is intrinsic);
by uniqueness of intrinsic derivatives this is the pointwise identity of continuous representatives. -/
theorem weakExtension_firstOrder_intrinsic (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Fl : Fin q → TypeOperator F 1}
    {Sl : Fin q → TypeOperator F 0}
    (hid : ∀ (l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
        (fun ξ => (Fl l).apply (sumSquaresWithDrift C.Xl u) ξ + (Sl l).apply u ξ))
    (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂) (hG : G.d = C.dl)
    (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderXCompact w C.Xl C.dl F.V 2 α u)
    {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D)
    (l : Fin q) :
    hasIntrinsicWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
      (fun ξ => (Fl l).apply (weakSumSquaresWithDrift D) ξ + (Sl l).apply u ξ) := by
  obtain ⟨hweak, hc⟩ := weakExtension_firstOrder_holder hF hw0 hw hid Ω₂ G hG hV hα0 hα1 hu hD l
  have hau : ContinuousOn (fun x => a x * u x) (F.V : Set (Fin (n + m) → ℝ)) :=
    a.continuous.continuousOn.mul (continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0 hu.1.1)
  exact hasIntrinsicWordDeriv_singleton_of_weak hF.lifted.contDiffOn_Xl l.succ hau hc hweak

end LiftedChart

end RothschildStein.P1

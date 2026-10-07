-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderInterpolationNoDriftNested
public import RothschildStein.P2.BaseHolderCalculus
public import RothschildStein.P1.LiftedDistanceGeometry
public import RothschildStein.P1.WeakExtensionHolder
public import RothschildStein.P2.TransferCoverCore
public import RothschildStein.S.WeakHolderToIntrinsic
public import RothschildStein.S.IntrinsicWeakHolderExport

/-!
# No drift: Hölder weak jets and the order-two norm

Part of the base Hölder estimate (BB pp. 577, 600-602), alphabet `Fin q`, all weights one, `L̃ = ∑ᵢ X̃ᵢ²`. On an open subset `V` of the
chart domain `C.U`, with the `(HD)` package of the lifted control distance (`LiftedChart.distanceGeometry`):

* `jetENormNoDrift d α V D = ∑_{|I| ≤ 2} ‖D I‖_{C^α(V)}` and its bound by the entries `[]`, `[l]`, `[i, l]`;
* `holderXENorm_eq_jetENormNoDrift`: for `u ∈ C^{2,α}_{X̃}(V)` and any Hölder weak jet `D` of `u` on `V`, the
  norm `‖u‖_{C^{2,α}(V)}` is `jetENormNoDrift` of `D`;
* `holderWeakJet_nil_eqOn_noDrift`, `holderWeakJet_hasIntrinsicWordDeriv_noDrift`,
  `exists_weakJet_of_memHolderX_noDrift`: the entry `D []` is `u`, the entries are intrinsic derivatives, and
  every `u ∈ C^{2,α}_{X̃}(V)` has a Hölder weak jet.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Jet

variable {N q : ℕ}

/-- No drift: the order-two Hölder norm computed on a jet: `∑_{|I| ≤ 2} ‖D I‖_{C^α(V)}`. -/
def jetENormNoDrift (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (α : ℝ) (V : Set (Fin N → ℝ))
    (D : List (Fin q) → (Fin N → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ I ∈ wordFamily noDriftWeight 2, holderENorm d α V (D I)

theorem jetENormNoDrift_mono_set {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ}
    {V V' : Set (Fin N → ℝ)} (h : V' ⊆ V) (D : List (Fin q) → (Fin N → ℝ) → ℝ) :
    jetENormNoDrift d α V' D ≤ jetENormNoDrift d α V D :=
  Finset.sum_le_sum fun _ _ => RothschildStein.S.holderENorm_mono d α V _ h

theorem jetENormNoDrift_congr {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ} {V : Set (Fin N → ℝ)}
    {D D' : List (Fin q) → (Fin N → ℝ) → ℝ}
    (h : ∀ I ∈ wordFamily noDriftWeight 2, EqOn (D I) (D' I) V) :
    jetENormNoDrift d α V D = jetENormNoDrift d α V D' :=
  Finset.sum_congr rfl fun I hI => RothschildStein.S.holderENorm_congr d α V _ (h I hI)

/-- The order-two norm of a jet is at most the norms of the entries `[]`, `[l]` and `[i, l]`. -/
theorem jetENormNoDrift_le (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (α : ℝ) (V : Set (Fin N → ℝ))
    (D : List (Fin q) → (Fin N → ℝ) → ℝ) :
    jetENormNoDrift d α V D ≤ holderENorm d α V (D []) +
      ∑ l : Fin q, holderENorm d α V (D [l]) +
        ∑ i : Fin q, ∑ l : Fin q, holderENorm d α V (D [i, l]) := by
  classical
  set f : List (Fin q) → ℝ≥0∞ := fun I => holderENorm d α V (D I) with hf
  have hsub : wordFamily noDriftWeight 2 ⊆
      (({[]} : Finset (List (Fin q))) ∪ (Finset.univ.image fun i : Fin q => [i])) ∪
        (Finset.univ.image fun p : Fin q × Fin q => [p.1, p.2]) := by
    intro K hK
    rcases wordFamily_noDrift_cases hK with rfl | ⟨i, rfl⟩ | ⟨j, i, rfl⟩
    · simp
    · simp
    · simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact Or.inr ⟨(j, i), rfl⟩
  have hinj1 : Function.Injective (fun i : Fin q => ([i] : List (Fin q))) := by
    intro i j h
    simpa using h
  have hinj2 : Function.Injective (fun p : Fin q × Fin q => ([p.1, p.2] : List (Fin q))) := by
    intro p p' h
    simp only [List.cons.injEq, and_true] at h
    exact Prod.ext h.1 h.2
  have hd1 : Disjoint ({[]} : Finset (List (Fin q)))
      (Finset.univ.image fun i : Fin q => [i]) := by
    rw [Finset.disjoint_left]
    intro K hK hK'
    simp only [Finset.mem_singleton] at hK
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hK'
    obtain ⟨i, rfl⟩ := hK'
    simp at hK
  have hd2 : Disjoint (({[]} : Finset (List (Fin q))) ∪
      (Finset.univ.image fun i : Fin q => [i]))
      (Finset.univ.image fun p : Fin q × Fin q => [p.1, p.2]) := by
    rw [Finset.disjoint_left]
    intro K hK hK'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hK'
    obtain ⟨p, rfl⟩ := hK'
    simp at hK
  unfold jetENormNoDrift
  calc ∑ I ∈ wordFamily noDriftWeight 2, holderENorm d α V (D I)
      ≤ ∑ I ∈ (({[]} : Finset (List (Fin q))) ∪
          (Finset.univ.image fun i : Fin q => [i])) ∪
          (Finset.univ.image fun p : Fin q × Fin q => [p.1, p.2]), f I :=
        Finset.sum_le_sum_of_subset hsub
    _ = f [] + ∑ i : Fin q, f [i] + ∑ p : Fin q × Fin q, f [p.1, p.2] := by
        rw [Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_singleton,
          Finset.sum_image (fun i _ j _ h => hinj1 h), Finset.sum_image (fun p _ p' _ h => hinj2 h)]
    _ = _ := by
        rw [Fintype.sum_prod_type]

end Jet

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m}

/-- No drift: the weak-jet entry for the empty word is the function itself, pointwise on `V`. -/
theorem holderWeakJet_nil_eqOn_noDrift {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U) {α : ℝ} (hα0 : 0 < α) {u : (Fin (n + m) → ℝ) → ℝ}
    {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ} (hu : ContinuousOn u (V : Set (Fin (n + m) → ℝ)))
    (hw : hasWeakWordDeriv C.Xl V [] u (D []))
    (hfin : holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (D []) < ⊤) :
    EqOn (D []) u (V : Set (Fin (n + m) → ℝ)) :=
  eqOn_of_hasWeakWordDeriv_of_continuousOn hw
    (S.hasWeakWordDeriv_nil C.Xl V (hu.locallyIntegrableOn V.isOpen.measurableSet))
    (LiftedChart.continuousOn_of_holderENorm_lt_top hV hα0 hfin) hu

/-- No drift: **the entries of a Hölder weak jet are intrinsic derivatives** (a weak jet whose
entries are continuous is the jet of intrinsic derivatives). -/
theorem holderWeakJet_hasIntrinsicWordDeriv_noDrift {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hu : ContinuousOn u (V : Set (Fin (n + m) → ℝ)))
    (hD : ∀ I ∈ wordFamily noDriftWeight 2, hasWeakWordDeriv C.Xl V I u (D I) ∧
      holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (D I) < ⊤) :
    ∀ I ∈ wordFamily noDriftWeight 2, hasIntrinsicWordDeriv C.Xl V I u (D I) := by
  classical
  intro I hI
  set D' : List (Fin q) → (Fin (n + m) → ℝ) → ℝ := fun J => if J = [] then u else D J
    with hD'
  have hsub : ∀ J, J.Sublist I → J ∈ wordFamily noDriftWeight 2 := fun J hJ =>
    (S.mem_wordFamily_iff noDriftWeight 2 J).mpr
      ((S.wordWeight_sublist_le noDriftWeight hJ).trans
        ((S.mem_wordFamily_iff noDriftWeight 2 I).mp hI))
  have hnil := holderWeakJet_nil_eqOn_noDrift (C := C) hV hα0 hu (hD [] (S.nil_mem_wordFamily _ _)).1
    (hD [] (S.nil_mem_wordFamily _ _)).2
  have key : hasIntrinsicWordDeriv C.Xl V I u (D' I) := by
    refine S.hasIntrinsicWordDeriv_of_continuous_weak_subwords V C.Xl hX I u D' (by simp [hD']) ?_ ?_
    · intro J hJ
      by_cases hJn : J = []
      · subst hJn
        simp only [hD', ite_true]
        exact S.hasWeakWordDeriv_nil C.Xl V (hu.locallyIntegrableOn V.isOpen.measurableSet)
      · simp only [hD', hJn, ite_false]
        exact (hD J (hsub J hJ)).1
    · intro J hJ
      by_cases hJn : J = []
      · subst hJn
        simpa only [hD', ite_true] using hu
      · simp only [hD', hJn, ite_false]
        exact LiftedChart.continuousOn_of_holderENorm_lt_top hV hα0 (hD J (hsub J hJ)).2
  by_cases hIn : I = []
  · subst hIn
    exact fun x hx => hnil hx
  · simpa only [hD', hIn, ite_false] using key

/-- No drift: **the order-two norm on a weak jet**: for `u ∈ C^{2,α}_{X̃}(V)` and any
Hölder weak jet `D` of `u` on the open `V ⊆ C.U`, `‖u‖_{C^{2,α}(V)} = ∑_I ‖D I‖_{C^α(V)}`. -/
theorem holderXENorm_eq_jetENormNoDrift {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderX noDriftWeight C.Xl C.dl V 2 α u)
    (hD : ∀ I ∈ wordFamily noDriftWeight 2, hasWeakWordDeriv C.Xl V I u (D I) ∧
      holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (D I) < ⊤) :
    holderXENorm noDriftWeight C.Xl C.dl V 2 α u =
      jetENormNoDrift C.dl α (V : Set (Fin (n + m) → ℝ)) D := by
  have h1 := S.holderXENorm_eq_weakHolderXENorm_of_memHolderX C.chartOpens V C.distanceGeometry hV
    noDriftWeight C.Xl hX 2 hα0 hu
  have h2 := S.weakHolderXENorm_eq_sum_representatives C.chartOpens V C.distanceGeometry hV
    noDriftWeight C.Xl 2 hα0 u D hD
  exact h1.trans h2

/-- No drift: every `u ∈ C^{2,α}_{X̃}(V)` on an open `V ⊆ C.U` has a Hölder weak jet `D` with
`D [] = u` and finite Hölder entries. -/
theorem exists_weakJet_of_memHolderX_noDrift {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderX noDriftWeight C.Xl C.dl V 2 α u) :
    ∃ D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ, D [] = u ∧
      ∀ I ∈ wordFamily noDriftWeight 2, hasWeakWordDeriv C.Xl V I u (D I) ∧
        holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (D I) < ⊤ := by
  have hw := S.memWeakHolderX_of_memHolderX C.chartOpens V C.distanceGeometry hV noDriftWeight C.Xl
    hX 2 hα0 hu
  exact S.exists_weakHolder_representatives noDriftWeight C.Xl C.dl V 2 α hw

end RothschildStein.P2

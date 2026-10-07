-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderCalculus
public import RothschildStein.P1.LiftedDistanceGeometry
public import RothschildStein.P1.WeakExtensionHolder
public import RothschildStein.P2.TransferCoverCore
public import RothschildStein.S.WeakHolderToIntrinsic
public import RothschildStein.S.IntrinsicWeakHolderExport

/-!
# Hölder weak jets and the order-two norm

Part of the base Hölder estimate (BB pp. 577, 600–602). On an open subset `V` of the chart domain `C.U`, with the `(HD)` package of
the lifted control distance (`LiftedChart.distanceGeometry`):

* `holderXENorm_eq_jetENorm`: for `u ∈ C^{2,α}_{X̃}(V)` and any Hölder weak jet `D` of `u` on `V`, the
  norm `‖u‖_{C^{2,α}(V)}` is `∑_I ‖D I‖_{C^α(V)}`;
* `holderWeakJet_nil_eqOn`: the entry `D []` is `u` pointwise;
* `holderWeakJet_hasIntrinsicWordDeriv`: the entries `D I` are intrinsic derivatives of `u`
  (continuous weak derivatives of subwords).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart driftWeight st Ω hΩ X x₀ m}

/-- The weak-jet entry for the empty word is the function itself, pointwise on `V`. -/
theorem holderWeakJet_nil_eqOn {V : Opens (Fin (n + m) → ℝ)} (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    {α : ℝ} (hα0 : 0 < α) {u : (Fin (n + m) → ℝ) → ℝ}
    {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hu : ContinuousOn u (V : Set (Fin (n + m) → ℝ)))
    (hw : hasWeakWordDeriv C.Xl V [] u (D []))
    (hfin : holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (D []) < ⊤) :
    EqOn (D []) u (V : Set (Fin (n + m) → ℝ)) :=
  eqOn_of_hasWeakWordDeriv_of_continuousOn hw
    (S.hasWeakWordDeriv_nil C.Xl V (hu.locallyIntegrableOn V.isOpen.measurableSet))
    (LiftedChart.continuousOn_of_holderENorm_lt_top hV hα0 hfin) hu

/-- **The entries of a Hölder weak jet are intrinsic derivatives** (a weak jet whose
entries are continuous is the jet of intrinsic derivatives). -/
theorem holderWeakJet_hasIntrinsicWordDeriv {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hu : ContinuousOn u (V : Set (Fin (n + m) → ℝ)))
    (hD : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl V I u (D I) ∧
      holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (D I) < ⊤) :
    ∀ I ∈ wordFamily driftWeight 2, hasIntrinsicWordDeriv C.Xl V I u (D I) := by
  classical
  intro I hI
  set D' : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ := fun J => if J = [] then u else D J
    with hD'
  have hsub : ∀ J, J.Sublist I → J ∈ wordFamily driftWeight 2 := fun J hJ =>
    (S.mem_wordFamily_iff driftWeight 2 J).mpr
      ((S.wordWeight_sublist_le driftWeight hJ).trans ((S.mem_wordFamily_iff driftWeight 2 I).mp hI))
  have hnil := holderWeakJet_nil_eqOn (C := C) hV hα0 hu (hD [] (S.nil_mem_wordFamily _ _)).1
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

/-- **The order-two norm on a weak jet**: for `u ∈ C^{2,α}_{X̃}(V)` and any Hölder
weak jet `D` of `u` on the open `V ⊆ C.U`, `‖u‖_{C^{2,α}(V)} = ∑_I ‖D I‖_{C^α(V)}`. The `(HD)` package
is the one of the lifted chart (`LiftedChart.distanceGeometry`). -/
theorem holderXENorm_eq_jetENorm {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderX driftWeight C.Xl C.dl V 2 α u)
    (hD : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl V I u (D I) ∧
      holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (D I) < ⊤) :
    holderXENorm driftWeight C.Xl C.dl V 2 α u = jetENorm C.dl α (V : Set (Fin (n + m) → ℝ)) D := by
  have h1 := S.holderXENorm_eq_weakHolderXENorm_of_memHolderX C.chartOpens V C.distanceGeometry hV
    driftWeight C.Xl hX 2 hα0 hu
  have h2 := S.weakHolderXENorm_eq_sum_representatives C.chartOpens V C.distanceGeometry hV
    driftWeight C.Xl 2 hα0 u D hD
  exact h1.trans h2

/-- The Hölder weak jet of a function of the class `C^{2,α}_{X̃}(V)`: every `u ∈ C^{2,α}_{X̃}(V)` on
an open `V ⊆ C.U` has a weak jet `D` with `D [] = u` and finite Hölder entries. -/
theorem exists_weakJet_of_memHolderX {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderX driftWeight C.Xl C.dl V 2 α u) :
    ∃ D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ, D [] = u ∧
      ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl V I u (D I) ∧
        holderENorm C.dl α (V : Set (Fin (n + m) → ℝ)) (D I) < ⊤ := by
  have hw := S.memWeakHolderX_of_memHolderX C.chartOpens V C.distanceGeometry hV driftWeight C.Xl
    hX 2 hα0 hu
  exact S.exists_weakHolder_representatives driftWeight C.Xl C.dl V 2 α hw

end RothschildStein.P2

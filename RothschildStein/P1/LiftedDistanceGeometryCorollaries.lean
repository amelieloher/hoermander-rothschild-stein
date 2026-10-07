-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedDistanceGeometry
public import RothschildStein.P1.WeakExtensionHolderMore
public import RothschildStein.P1.HigherNormHolderJets
public import RothschildStein.P1.GainHolder

/-!
# Discharging the lifted `(HD)` hypothesis of the Hölder extension theorems

Each gain or weak-extension theorem below that takes an `(HD1)`-`(HD2)` package `G : S.DistanceGeometry Ω₂`
of the lifted control distance (`hG : G.d = C.dl`, `hV : V ⊆ Ω₂`) is restated without it:
`Ω₂ := C.chartOpens`, `G := C.distanceGeometry` (`LiftedChart.distanceGeometry`),
`hG := rfl`, and `hV` from `V ⊆ closure V ⊆ C.U` (`IsLiftedFrame.closure_subset`). The statements are
those of the original theorems, with exactly these four hypotheses removed; the proofs apply the
original theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace LiftedChart

/-- The cutoff region of a lifted frame lies in the chart domain `C.chartOpens`
(the discharge of `hV : V ⊆ Ω₂` for `Ω₂ := C.chartOpens`). -/
theorem IsLiftedFrame.subset_chartOpens {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
    {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
    {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} (hF : C.IsLiftedFrame F) :
    (F.V : Set (Fin (n + m) → ℝ)) ⊆ (C.chartOpens : Set (Fin (n + m) → ℝ)) :=
  hF.subset_U

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- `memSobolevXZero_of_holder` with the `(HD1)`-`(HD2)` package
of the lifted control distance (`LiftedChart.distanceGeometry`) supplied: the statement of `memSobolevXZero_of_holder`
without the hypotheses `Ω₂`, `G`, `hG : G.d = C.dl`, `hV : V ⊆ Ω₂` (instantiated with
`C.chartOpens`, `C.distanceGeometry`, `rfl`, `V ⊆ C.U`). -/
theorem memSobolevXZero_of_holder_lifted (hF : C.IsStandardFrame F H K hQ)
    {α : ℝ} (hα0 : 0 < α)
    {kk : ℕ} {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderXCompact w C.Xl C.dl F.V kk α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V kk α u D) :
    memSobolevXZero w C.Xl F.V kk 2 u ∧ IsWeakJet w C.Xl F.V kk 2 u D :=
  memSobolevXZero_of_holder hF C.chartOpens C.distanceGeometry rfl hF.lifted.subset_chartOpens hα0
    hu hD

end LiftedChart

namespace LiftedChart

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

end LiftedChart

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- `weakExtension_higher_holder` with the `(HD1)`-`(HD2)` package of the lifted control
distance (`LiftedChart.distanceGeometry`) supplied: the statement of `weakExtension_higher_holder` without the
hypotheses `Ω₂`, `G`, `hG : G.d = C.dl`, `hV : V ⊆ Ω₂` (instantiated with `C.chartOpens`,
`C.distanceGeometry`, `rfl`, `V ⊆ C.U`). -/
theorem weakExtension_higher_holder_lifted (hF : C.IsStandardFrame F H K hQ) (hw : ∀ j, (w j : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} (I : List (Fin k)) (hI : 2 ≤ I.length)
    {Sf Tf : List (Fin k) → TypeOperator F 0}
    (hid : ∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
        (fun ξ => (∑ J ∈ repWords k (I.length - 2),
            (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (u : (Fin (n + m) → ℝ) → ℝ))) ξ) +
          ∑ K ∈ repWords k (I.length - 1),
            (Tf K).apply (wordDerivative C.Xl K (u : (Fin (n + m) → ℝ) → ℝ)) ξ))
    {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderXCompact w C.Xl C.dl F.V I.length α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsHolderWeakJet w C.Xl C.dl F.V I.length α u D) :
    hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
      (fun ξ => (∑ J ∈ repWords k (I.length - 2), (Sf J).apply (weakSumSquares D J) ξ) +
        ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (D K) ξ) ∧
    ContinuousOn (fun ξ => (∑ J ∈ repWords k (I.length - 2), (Sf J).apply (weakSumSquares D J) ξ) +
        ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (D K) ξ) (F.V : Set (Fin (n + m) → ℝ)) :=
  weakExtension_higher_holder hF hw I hI hid C.chartOpens C.distanceGeometry rfl
    hF.lifted.subset_chartOpens hα0 hα1 hu hD

end LiftedChart

end RothschildStein.P1

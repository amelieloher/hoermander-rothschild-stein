-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedDistanceGeometryCorollaries
public import RothschildStein.P1.WeakExtensionMain

/-!
# Weak extension assembled, with the lifted `(HD)` package discharged

`weakExtension_*_full_of` of `WeakExtensionMain` restated with the Hölder clause free of the hypotheses
`Ω₂`, `G`, `G.d = C.dl`, `V ⊆ Ω₂` (instantiated with `C.chartOpens`, `C.distanceGeometry`); the other
clauses and the conditional hypotheses are unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

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

/-- `weakExtension_higher_full_of` with the `(HD1)`-`(HD2)` package of the lifted control
distance (`LiftedChart.distanceGeometry`) supplied: the same statement, with the Hölder clause stated without the
hypotheses `Ω₂`, `G`, `G.d = C.dl`, `V ⊆ Ω₂` (instantiated with `C.chartOpens`,
`C.distanceGeometry`, `rfl`, `V ⊆ C.U`). -/
theorem weakExtension_higher_full_of_lifted (hF : C.IsStandardFrame F H K hQ) (hw : ∀ j, (w j : ℕ) = 1)
    (B : Fin (n + m) → List (Fin k)) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w C.Xl)
    (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl) (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (I : List (Fin k)) (hI : 2 ≤ I.length) :
    ∃ Sf Tf : List (Fin k) → TypeOperator F 0,
      (∀ J, IsEndpoint F C.Xl (Sf J)) ∧ (∀ K, IsEndpoint F C.Xl (Tf K)) ∧
      (∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (u : (Fin (n + m) → ℝ) → ℝ))) ξ) +
            ∑ K ∈ repWords k (I.length - 1),
              (Tf K).apply (wordDerivative C.Xl K (u : (Fin (n + m) → ℝ) → ℝ)) ξ)) ∧
      (∀ u : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ)) →
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl u)) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (wordDerivative C.Xl K u) ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V I.length P u → IsWeakJet w C.Xl F.V I.length P u D →
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).lpAct hF hP1 hP (weakSumSquares D J) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).lpAct hF hP1 hP (D K) ξ)) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memHolderXCompact w C.Xl C.dl F.V I.length α u →
        ∀ D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ,
        IsHolderWeakJet w C.Xl C.dl F.V I.length α u D →
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2), (Sf J).apply (weakSumSquares D J) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (D K) ξ) ∧
        ContinuousOn (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).apply (weakSumSquares D J) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (D K) ξ) (F.V : Set (Fin (n + m) → ℝ))) := by
  obtain ⟨Sf, Tf, hS, hT, hid, hext⟩ :=
    weakExtension_higher_of hF hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix I hI
  exact ⟨Sf, Tf, hS, hT, hid, fun u hu => weakExtension_higher_smooth hF I hid hu, hext,
    fun α hα0 hα1 u hu D hD =>
      weakExtension_higher_holder_lifted hF hw I hI hid hα0 hα1 hu hD⟩

end LiftedChart

end RothschildStein.P1

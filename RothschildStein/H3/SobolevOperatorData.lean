-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakDriftOperatorData
public import RothschildStein.H3.WeakOperatorPairing
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- Local Sobolev membership supplies all jets needed for the
actual weak operator; no operator regularity premise is added. -/
theorem exists_weakDriftOperatorData {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u) :
    Nonempty (WeakDriftOperatorData X Ω p u) := by
  classical
  have hi : ∀ i : Fin (q+1), [i] ∈ wordFamily driftWeight 2 := by
    intro i
    by_cases he : i = 0
    · subst i
      simp [S.mem_wordFamily_iff,wordWeight,driftWeight]
    · simp [S.mem_wordFamily_iff,wordWeight,driftWeight,he]
  have hii : ∀ i : Fin q, [i.succ,i.succ] ∈ wordFamily driftWeight 2 := by
    intro i
    simp [S.mem_wordFamily_iff,wordWeight,driftWeight,Fin.succ_ne_zero]
  choose g hg hgp using fun i => hu.2 [i] (hi i)
  choose h hh hhp using fun i => hu.2 [i.succ,i.succ] (hii i)
  exact ⟨⟨g,h,hg,hgp,hh,hhp⟩⟩

/-- The weak operator belongs to the same local Lp class as its jets. -/
theorem WeakDriftOperatorData.operator_memLp {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u) :
    MemLp D.operator p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  have hs := memLp_finsetSum Finset.univ (fun i _ => D.square_memLp i)
  convert (D.first_memLp 0).add hs using 1
  funext x
  simp only [WeakDriftOperatorData.operator,Pi.add_apply]

/-- The chosen Sobolev operator has the exact fixed transpose pairing. -/
theorem WeakDriftOperatorData.operator_pairing {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), D.operator x*ψ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), u x*sumSquaresWithDriftTranspose X ψ x :=
  integral_sumSquaresWithDrift_weak_jets X Ω hX u D.first D.square D.first_weak D.square_weak ψ

end RothschildStein.H3

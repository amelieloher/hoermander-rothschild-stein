-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.noDriftWeight
public import Mathlib.Tactic.Linter

/-!
# Local square integrability of horizontal weak derivatives

First-order horizontal Sobolev membership supplies square-integrable weak
representatives. Uniqueness identifies these with any separately specified weak
derivatives on the same open set. See Bramanti–Brandolini, Definition 2.2, p. 68.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal
open RothschildStein

namespace HeatKernel

/-- With unit weights, first-order words are exactly the empty word and single letters. -/
theorem mem_wordFamily_noDrift_one_iff {m : ℕ} (I : List (Fin m)) :
    I ∈ wordFamily noDriftWeight 1 ↔ I = [] ∨ ∃ i, I = [i] := by
  rw [RothschildStein.S.mem_wordFamily_iff]
  have hw : wordWeight noDriftWeight I = I.length := by
    simp [wordWeight, noDriftWeight]
  rw [hw]
  cases I with
  | nil => simp
  | cons i I =>
    cases I with
    | nil => simp
    | cons j J => simp

/-- First-order horizontal Sobolev membership is square integrability of the function and its weak gradient. -/
theorem memSobolevX_noDrift_one_two_iff {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {V : Opens (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ} :
    memSobolevX noDriftWeight X V 1 2 u ↔
      MemLp u 2 (volume.restrict (V : Set (Fin n → ℝ))) ∧
      ∀ i, ∃ g, hasWeakWordDeriv X V [i] u g ∧
        MemLp g 2 (volume.restrict (V : Set (Fin n → ℝ))) := by
  constructor
  · intro h
    exact ⟨h.1, fun i => h.2 [i] ((mem_wordFamily_noDrift_one_iff [i]).2
      (Or.inr ⟨i, rfl⟩))⟩
  · rintro ⟨hu, hg⟩
    refine ⟨hu, fun I hI => ?_⟩
    rcases (mem_wordFamily_noDrift_one_iff I).1 hI with rfl | ⟨i, rfl⟩
    · refine ⟨u, RothschildStein.S.hasWeakWordDeriv_nil X V ?_, hu⟩
      exact locallyIntegrableOn_of_locallyIntegrable_restrict
        (hu.locallyIntegrable (by norm_num))
    · exact hg i

/-- Every weak derivative in the weighted family inherits the Sobolev integrability. -/
theorem memLp_of_memSobolevX_of_hasWeakWordDeriv {m n : ℕ}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {V : Opens (Fin n → ℝ)} {k : ℕ} {p : ℝ≥0∞}
    {u g : (Fin n → ℝ) → ℝ} {I : List (Fin m)}
    (hu : memSobolevX w X V k p u) (hI : I ∈ wordFamily w k)
    (hg : hasWeakWordDeriv X V I u g) :
    MemLp g p (volume.restrict (V : Set (Fin n → ℝ))) := by
  obtain ⟨v, hv, hLp⟩ := hu.2 I hI
  exact hLp.ae_eq (RothschildStein.S.hasWeakWordDeriv_unique X V hv hg)

/-- A local first-order horizontal Sobolev function has local square-integrable derivatives. -/
theorem memLp_two_horizontal_of_memSobolevXLoc {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω V : Opens (Fin n → ℝ)} {u g : (Fin n → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight X Ω 1 2 u)
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hsub : closure (V : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (i : Fin m) (hg : hasWeakWordDeriv X Ω [i] u g) :
    MemLp g 2 (volume.restrict (V : Set (Fin n → ℝ))) := by
  apply memLp_of_memSobolevX_of_hasWeakWordDeriv (I := [i]) (hu V hV hsub)
  · simp [RothschildStein.S.mem_wordFamily_iff, wordWeight, noDriftWeight]
  · exact RothschildStein.S.hasWeakWordDeriv_restrict X Ω V
      (subset_closure.trans hsub) hg

/-- Local first-order Sobolev membership supplies all horizontal derivatives simultaneously. -/
theorem exists_horizontal_derivatives_of_memSobolevXLoc {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω V : Opens (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight X Ω 1 2 u)
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hsub : closure (V : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ))) :
    MemLp u 2 (volume.restrict (V : Set (Fin n → ℝ))) ∧
      ∃ g : Fin m → (Fin n → ℝ) → ℝ, ∀ i,
        hasWeakWordDeriv X V [i] u (g i) ∧
        MemLp (g i) 2 (volume.restrict (V : Set (Fin n → ℝ))) := by
  have h := hu V hV hsub
  refine ⟨h.1, ?_⟩
  have hi : ∀ i : Fin m, ∃ g, hasWeakWordDeriv X V [i] u g ∧
      MemLp g 2 (volume.restrict (V : Set (Fin n → ℝ))) := by
    intro i
    exact h.2 [i] (by
      simp [RothschildStein.S.mem_wordFamily_iff, wordWeight, noDriftWeight])
  exact Classical.axiomOfChoice hi

/-- A separately specified horizontal derivative is square-integrable on every compact subset. -/
theorem memLp_two_horizontal_on_compact_of_memSobolevXLoc {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {u g : (Fin n → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight X Ω 1 2 u)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hsub : K ⊆ Ω)
    (i : Fin m) (hg : hasWeakWordDeriv X Ω [i] u g) :
    MemLp g 2 (volume.restrict K) := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hsub
  have hLp := memLp_two_horizontal_of_memSobolevXLoc
    (V := ⟨V, hV⟩) hu hVc hVU i hg
  exact hLp.mono_measure (Measure.restrict_mono hKV le_rfl)

/-- A local horizontal Sobolev function is square-integrable on every compact subset. -/
theorem memLp_two_on_compact_of_memSobolevXLoc {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight X Ω 1 2 u)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hsub : K ⊆ Ω) :
    MemLp u 2 (volume.restrict K) := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hsub
  exact (hu ⟨V, hV⟩ hVc hVU).1.mono_measure (Measure.restrict_mono hKV le_rfl)

end HeatKernel

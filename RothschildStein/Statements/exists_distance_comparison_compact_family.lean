-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.bracketStepOn
public import RothschildStein.Definitions.controlDistance
public import RothschildStein.Definitions.rsBall
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.absoluteJacobian
public import RothschildStein.Definitions.wordFamily
public import RothschildStein.Provider.exists_distance_comparison_compact_family

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein

/-- Comparison of the control distance d with the short-word distance d*,
uniform over a compact parameter family (BB Thm 9.6 and Remark 9.5; NSW Acta 155 Thms 2–4). -/
theorem exists_distance_comparison_compact_family
    {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg]
    {k n s : ℕ} (hn : 0 < n)
    (w : Fin (k + 1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hVΩ : V ⊆ Ω)
    (X : Sg → Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hjoint : ∀ i j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ Ω))
    (hstep : ∀ σ, bracketStepOn V w (X σ) s) :
    let e : Fin (wordFamily w s).card → List (Fin (k + 1)) :=
      fun j => ((wordFamily w s).equivFin.symm j).val
    let ws : Fin (wordFamily w s).card → ℕ+ := fun j => Nat.toPNat' (wordWeight w (e j))
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ σ, ∀ x ∈ K, ∀ y : Fin n → ℝ,
        controlDistance Ω ws (fun j => wordBracket (X σ) (e j)) x y < ENNReal.ofReal ε →
        controlDistance Ω ws (fun j => wordBracket (X σ) (e j)) x y ≤
            controlDistance Ω w (X σ) x y ∧
          controlDistance Ω w (X σ) x y ≤
            ENNReal.ofReal C * controlDistance Ω ws (fun j => wordBracket (X σ) (e j)) x y :=
  by exact RothschildStein.Provider.exists_distance_comparison_compact_family hn w hw hΩ hV hK hKV hVΩ X hX hjoint hstep

end RothschildStein

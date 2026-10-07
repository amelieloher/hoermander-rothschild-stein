-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevWordApproximation
public import RothschildStein.Definitions.memSobolevXZero
public import RothschildStein.S.WeakSub
public import RothschildStein.S.SobolevCutoffZero

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- The literal global zero-boundary Sobolev predicate
supplies the full word approximation interface, independently of the
chosen weak representatives. -/
theorem exists_sobolevWordApproximation_of_memSobolevXZero {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXZero w X ⊤ 2 p u) :
    Nonempty (SobolevWordApproximation w X p u) := by
  obtain ⟨hSob, φ, hlim⟩ := hu
  have hword (I : List (Fin m)) (hI : I ∈ wordFamily w 2)
      (g : (Fin N → ℝ) → ℝ) (hg : hasWeakWordDeriv X ⊤ I u g) :
      Tendsto (fun j => eLpNorm (wordDerivative X I (φ j) - g) p volume) atTop (𝓝 0) := by
    have hb (j : ℕ) : eLpNorm (wordDerivative X I (φ j) - g) p volume ≤
        sobolevXENorm w X ⊤ 2 p (fun x => u x - φ j x) := by
      have hc := S.hasWeakWordDeriv_classical ⊤ X (fun i => (hX i).contDiffOn) I (φ j)
        (φ j).contDiff.contDiffOn
      have hd := S.hasWeakWordDeriv_sub X ⊤ (fun i => (hX i).contDiffOn) hg hc
      have hn := Finset.single_le_sum
        (fun J _ => (show (0 : ℝ≥0∞) ≤ weakWordENorm X ⊤ J p (fun x => u x - φ j x) from bot_le)) hI
      change weakWordENorm X ⊤ I p (fun x => u x - φ j x) ≤ _ at hn
      rw [S.weakWordENorm_eq X ⊤ I p _ _ hd] at hn
      rw [eLpNorm_sub_comm]
      have he : g - wordDerivative X I (φ j) = (fun x => g x - wordDerivative X I (φ j) x) := by
        funext x
        rfl
      rw [he]
      simpa only [sobolevXENorm, Opens.coe_top, Measure.restrict_univ] using hn
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hb
  have hnil : hasWeakWordDeriv X ⊤ [] u u := S.hasWeakWordDeriv_nil X ⊤
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hSob.1.locallyIntegrable Fact.out))
  refine ⟨{ functions := fun j => φ j
            smooth := fun j => (φ j).contDiff
            compact := fun j => (φ j).hasCompactSupport
            zero := ?_
            word := ?_ }⟩
  · simpa only [wordDerivative] using hword [] (by simp [S.mem_wordFamily_iff, wordWeight]) u hnil
  · intro I hI g hg _hgp
    exact hword I hI g hg

end RothschildStein.H3

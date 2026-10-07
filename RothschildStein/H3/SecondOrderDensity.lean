-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WordEstimateDensity
public import RothschildStein.H3.SobolevOperatorData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The weighted second-order estimates for Sobolev inputs under the
compact estimate and global density hypotheses. The operator is an Lp
function paired with the fixed transpose (BB Proposition 8.28, p. 361). -/
theorem second_orders_of_compact_and_density {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (C : ℝ)
    (hcompact : ∀ v : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative X I v) p volume ≤
          ENNReal.ofReal C*eLpNorm (sumSquaresWithDrift X v) p volume)
    (hdensity : ∀ u, memSobolevX driftWeight X ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight X p u))
    (u : (Fin n → ℝ) → ℝ) (hu : memSobolevX driftWeight X ⊤ 2 p u) :
    ∃ D : WeakDriftOperatorData X ⊤ p u,
      MemLp D.operator p volume ∧
      (∀ ψ : TestFunction (⊤ : Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞),
        (∫ x, D.operator x*ψ x) = ∫ x, u x*sumSquaresWithDriftTranspose X ψ x) ∧
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        weakWordENorm X ⊤ I p u ≤ ENNReal.ofReal C*eLpNorm D.operator p volume := by
  obtain ⟨D⟩ := exists_weakDriftOperatorData X ⊤ p u hu
  refine ⟨D,by simpa using D.operator_memLp,?_,?_⟩
  · intro ψ
    simpa using D.operator_pairing (fun i => (hX i).contDiffOn) ψ
  · intro I hI
    have hi : I ∈ wordFamily driftWeight 2 := by
      simp [S.mem_wordFamily_iff,hI]
    have hgp₀ : MemLp (D.first 0) p volume := by simpa using D.first_memLp 0
    have hgp : ∀ i, MemLp (D.square i) p volume := fun i => by simpa using D.square_memLp i
    have hb := word_estimate_of_compact_and_density X hX p hp I hi C
      (fun v hv hvc => hcompact v hv hvc I hI) hdensity u (D.first 0) D.square hu
      (D.first_weak 0) hgp₀ D.square_weak hgp
    have he : D.operator = D.first 0+∑ i, D.square i := by
      funext x
      simp only [WeakDriftOperatorData.operator,Pi.add_apply,Finset.sum_apply]
    rw [he]
    exact hb

end RothschildStein.H3

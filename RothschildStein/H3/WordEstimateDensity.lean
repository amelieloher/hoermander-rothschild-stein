-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevOperatorApproximation
public import RothschildStein.H3.CompactOperatorLp
public import RothschildStein.H3.LpEstimateLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal BigOperators

/-- The compact-test estimate for a word passes to Sobolev inputs by
global density. The operator limit follows from its weak drift and square
jets (BB pp. 360–361). -/
theorem word_estimate_of_compact_and_density {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (I : List (Fin (q+1)))
    (hI : I ∈ wordFamily driftWeight 2) (C : ℝ)
    (hcompact : ∀ v : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      eLpNorm (wordDerivative X I v) p volume ≤
        ENNReal.ofReal C*eLpNorm (sumSquaresWithDrift X v) p volume)
    (hdensity : ∀ u, memSobolevX driftWeight X ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight X p u))
    (u g₀ : (Fin n → ℝ) → ℝ) (g : Fin q → (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X ⊤ 2 p u)
    (hg₀ : hasWeakWordDeriv X ⊤ [0] u g₀) (hgp₀ : MemLp g₀ p volume)
    (hg : ∀ i : Fin q, hasWeakWordDeriv X ⊤ [i.succ,i.succ] u (g i))
    (hgp : ∀ i, MemLp (g i) p volume) :
    weakWordENorm X ⊤ I p u ≤ ENNReal.ofReal C*eLpNorm (g₀+∑ i, g i) p volume := by
  obtain ⟨z,hz,hzp⟩ := hu.2 I hI
  have hzp' : MemLp z p volume := by simpa using hzp
  obtain ⟨A⟩ := hdensity u hu
  have hop : MemLp (g₀+∑ i, g i) p volume := by
    apply hgp₀.add
    convert memLp_finsetSum Finset.univ (fun i _ => hgp i) using 1
    funext x
    simp only [Finset.sum_apply]
  have hlimit := lp_estimate_of_approximation volume hp hop hzp'
    (fun k => memLp_sumSquaresWithDrift_compact X hX (A.functions k) (A.smooth k) (A.compact k) p)
    (fun k => memLp_wordDerivative_compact X hX I (A.smooth k) (A.compact k) p)
    (sumSquaresWithDrift_approximation_tendsto X p hp u g₀ g hg₀ hgp₀ hg hgp A)
    (A.word I hI z hz hzp') C
    (fun k => hcompact (A.functions k) (A.smooth k) (A.compact k))
  rw [S.weakWordENorm_eq X ⊤ I p u z hz]
  simpa using hlimit

end RothschildStein.H3

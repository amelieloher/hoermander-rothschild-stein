-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionAffine
public import HeatKernel.Moser.HarnackOscillation

/-! # Oscillation of bounded local weak solutions

A Harnack estimate for nonnegative solutions applies to both affine shifts of a bounded
solution. The earlier and later region measures and their inclusions are explicit.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- A Harnack estimate on two interior regions implies oscillation contraction for every
bounded local weak solution, using the same coefficient field. -/
theorem IsLocalWeakSolution.oscillation_le_of_harnack_estimate {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {μ ν : Measure (ℝ × (Fin N → ℝ))} {H : ℝ}
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hμsub : μ ≤ volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))))
    (hνsub : ν ≤ volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))))
    (hH : 1 ≤ H)
    (harnack : ∀ w : ℝ → (Fin N → ℝ) → ℝ,
      IsLocalWeakSolution G hq hqpos hw hspan a I U w →
      (∀ᵐ z ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))), 0 ≤ w z.1 z.2) →
      essSup (fun z => ENNReal.ofReal (w z.1 z.2)) μ ≤
        ENNReal.ofReal H * essInf (fun z => ENNReal.ofReal (w z.1 z.2)) ν)
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) {m M : ℝ}
    (hbound : ∀ᵐ z ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))),
      m ≤ u z.1 z.2 ∧ u z.1 z.2 ≤ M) :
    essSup (Function.uncurry u) ν - essInf (Function.uncurry u) ν ≤
      (1 - 1 / (2 * H)) * (M - m) := by
  have hl := harnack (fun t x => u t x - m)
    (IsLocalWeakSolution.sub_const G hq hqpos hw hspan hu m)
    (hbound.mono fun _ h => sub_nonneg.mpr h.1)
  have hr := harnack (fun t x => M - u t x)
    (IsLocalWeakSolution.const_sub G hq hqpos hw hspan hu M)
    (hbound.mono fun _ h => sub_nonneg.mpr h.2)
  exact essSup_sub_essInf_le_of_shifted_ofReal_harnack hμ hν (lt_of_lt_of_le zero_lt_one hH)
    (hbound.filter_mono (ae_mono hμsub)) (hbound.filter_mono (ae_mono hνsub)) hl hr

/-- The same Harnack estimate reduces the essential oscillation of an essentially
bounded local weak solution from the outer region to the later region. -/
theorem IsLocalWeakSolution.essential_oscillation_le_of_harnack_estimate {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {μ ν : Measure (ℝ × (Fin N → ℝ))} {H : ℝ}
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hμsub : μ ≤ volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))))
    (hνsub : ν ≤ volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))))
    (hH : 1 ≤ H)
    (harnack : ∀ w : ℝ → (Fin N → ℝ) → ℝ,
      IsLocalWeakSolution G hq hqpos hw hspan a I U w →
      (∀ᵐ z ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))), 0 ≤ w z.1 z.2) →
      essSup (fun z => ENNReal.ofReal (w z.1 z.2)) μ ≤
        ENNReal.ofReal H * essInf (fun z => ENNReal.ofReal (w z.1 z.2)) ν)
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (hupper : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))))) (Function.uncurry u))
    (hlower : Filter.IsBoundedUnder (· ≥ ·)
      (ae (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))))) (Function.uncurry u)) :
    essSup (Function.uncurry u) ν - essInf (Function.uncurry u) ν ≤
      (1 - 1 / (2 * H)) *
        (essSup (Function.uncurry u)
          (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))) -
         essInf (Function.uncurry u)
          (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))))) := by
  apply IsLocalWeakSolution.oscillation_le_of_harnack_estimate G hq hqpos hw hspan
    hμ hν hμsub hνsub hH harnack hu
  filter_upwards [ae_essInf_le hlower, ae_le_essSup hupper] with z hzlo hzhi
  exact ⟨hzlo, hzhi⟩

end HeatKernel

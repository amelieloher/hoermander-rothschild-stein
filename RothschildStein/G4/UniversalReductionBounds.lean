-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ReductionValueJets
public import RothschildStein.G4.CompositionJetBounds
public import RothschildStein.G4.PiJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Universal quantitative reduction from a joint coefficient-jet
budget. The constant is chosen before the domain and actual vector fields,
so its dependencies are precisely the displayed numerical data. -/
theorem exists_universal_reduction_jet_bound (p n h : ℕ) (H P Δ : ℝ)
    (hP : 0 ≤ P) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (Z : Fin p → (Fin n → ℝ) → (Fin n → ℝ))
        (V : (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (Z I) Ω) →
      ContDiffOn ℝ (⊤ : ℕ∞) V Ω →
      (∀ x ∈ Ω, determinantSquareSum Z x ≠ 0) →
      (∀ x ∈ K, ‖Sum.elim (fun I => Z I x) (fun _ : Unit => V x)‖ ≤ H) →
      (∀ x ∈ K, Δ ^ 2 ≤ determinantSquareSum Z x) →
      HasJetBound Ω K (fun x => Sum.elim (fun I => Z I x) (fun _ : Unit => V x)) h P →
      ∀ J, HasJetBound Ω K (reductionCoefficient Z V J) h C := by
  obtain ⟨B, hB, hbound⟩ := exists_valueReduction_jet_bound p n h H Δ hΔ
  refine ⟨1 + compositionJetBudget h B P, ?_, ?_⟩
  · have hn : 0 ≤ compositionJetBudget h B P := by
      unfold compositionJetBudget
      exact Finset.sum_nonneg (fun j _ => by positivity)
    linarith
  · intro Ω K hΩ hKΩ Z V hZ hV hspan hnorm hdet hjets J
    let f : (Fin n → ℝ) → ReductionValues p n :=
      fun x => Sum.elim (fun I => Z I x) (fun _ : Unit => V x)
    have hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω := by
      apply contDiffOn_pi.mpr
      intro a
      cases a with
      | inl I => exact hZ I
      | inr u => exact hV
    have hmap : MapsTo f Ω {u | valueDenominator u ≠ 0} := by
      intro x hx
      exact hspan x hx
    have hKL : MapsTo f K (Metric.closedBall 0 H ∩ {u | Δ ^ 2 ≤ valueDenominator u}) := by
      intro x hx
      refine ⟨?_, hdet x hx⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm x hx
    have hb := hjets.comp hΩ valueDenominator_domain_isOpen hKΩ hf
      (valueReduction_contDiffOn J) hmap hKL hP hB.le (hbound J)
    intro j hj x hx
    have hh := hb j hj x hx
    change ‖iteratedFDerivWithin ℝ j (reductionCoefficient Z V J) Ω x‖ ≤ _ at hh
    exact hh.trans (by linarith)

/-- Component jet budgets suffice for the universal global
reduction bound. The constant is uniform over all actual field families. -/
theorem exists_universal_reduction_component_jet_bound (p n h : ℕ) (H P Δ : ℝ)
    (hP : 0 ≤ P) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (Z : Fin p → (Fin n → ℝ) → (Fin n → ℝ))
        (V : (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (Z I) Ω) →
      ContDiffOn ℝ (⊤ : ℕ∞) V Ω →
      (∀ x ∈ Ω, determinantSquareSum Z x ≠ 0) →
      (∀ x ∈ K, ‖Sum.elim (fun I => Z I x) (fun _ : Unit => V x)‖ ≤ H) →
      (∀ x ∈ K, Δ ^ 2 ≤ determinantSquareSum Z x) →
      (∀ I, HasJetBound Ω K (Z I) h P) → HasJetBound Ω K V h P →
      ∀ J, HasJetBound Ω K (reductionCoefficient Z V J) h C := by
  obtain ⟨C, hC, hbound⟩ := exists_universal_reduction_jet_bound p n h H P Δ hP hΔ
  refine ⟨C, hC, ?_⟩
  intro Ω K hΩ hKΩ Z V hZ hV hspan hnorm hdet hjets hVjets
  apply hbound Ω K hΩ hKΩ Z V hZ hV hspan hnorm hdet
  refine HasJetBound.pi hΩ hKΩ ?_ hP ?_
  · intro a
    cases a with
    | inl I => exact hZ I
    | inr u => exact hV
  · intro a
    cases a with
    | inl I => exact hjets I
    | inr u => exact hVjets

end RothschildStein.G4

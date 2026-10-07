-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.TriangularBracketProjection
public import RothschildStein.G1.FlowUniqueness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.L1

/-- Actual constant word-coefficient flow trajectories
intertwine with horizontal projection on their whole time interval.
This applies to the selected and completed G4 frames without requiring
an endpoint identity as a premise (BB pp. 517, 520–521). -/
theorem word_flow_projection_eqOn {ι : Type*} [Fintype ι] {q n m : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin q → Fin m → MvPolynomial (Fin (n+m)) ℝ)
    (I : ι → List (Fin q)) (c : ι → ℝ)
    (α : ℝ → (Fin (n+m) → ℝ)) (β : ℝ → (Fin n → ℝ))
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hα : ∀ t ∈ Ioo a b,
      HasDerivAt α (∑ i, c i • wordBracket (triangularLift X P) (I i) (α t)) t ∧
        α t ∈ basePoint ⁻¹' Ω)
    (hβ : ∀ t ∈ Ioo a b,
      HasDerivAt β (∑ i, c i • wordBracket X (I i) (β t)) t ∧ β t ∈ Ω)
    (heq : basePoint (α t₀) = β t₀) :
    EqOn (fun t => basePoint (α t)) β (Ioo a b) := by
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ∑ i, c i • wordBracket X (I i) x) Ω :=
    ContDiffOn.sum (fun i _ => (G1.wordBracket_contDiffOn hΩ X hX (I i)).const_smul (c i))
  apply G1.integralCurve_eqOn hΩ hZ ht₀ _ hβ heq
  intro t ht
  refine ⟨?_,(hα t ht).2⟩
  have hd := (P1.paddingBaseCLM n m).hasFDerivAt.comp_hasDerivAt t (hα t ht).1
  have hv : P1.paddingBaseCLM n m
      (∑ i, c i • wordBracket (triangularLift X P) (I i) (α t)) =
      ∑ i, c i • wordBracket X (I i) (basePoint (α t)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, P1.paddingBaseCLM_apply,
      wordBracket_triangularLift_projection hΩ X hX P (I i) _ (hα t ht).2]
  simpa only [Function.comp_def, P1.paddingBaseCLM_apply, hv] using hd

end RothschildStein.L1

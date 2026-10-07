-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Assembly.LocalRepresentative
public import Hormander.F.CountableGluing
public import Hormander.F.EdgeCases

/-!
# Assembly of Hörmander's theorem from the local hypotheses

Under the local regularity estimate and localized forcing identity hypotheses, the conclusion
holds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hormander.F

/-- Hörmander's theorem on `Fin N → ℝ`, assuming the local regularity estimate and localized forcing identity
for every local patch. -/
theorem exists_smooth_aeRepresentative_of_E4_forcing
    {k N : ℕ} {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c g u : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hspan : Hormander.Interface.LieAlgebraSpansOn Ω X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hEq : Hormander.Interface.HasWeakHormanderEquation Ω X c g u)
    (hE4 : E4Statement)
    (hF4 : ∀ (hN : 0 < N) (x₀ : Fin N → ℝ),
      ∀ P : LocalPatch hN (coordinateEquiv N '' Ω) (pushVectorFields X)
        (fun y => c ((coordinateEquiv N).symm y)) (coordinateEquiv N x₀),
        LocalizedForcingStatement hN X c g u x₀ P) :
    ∃ f : (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f := by
  by_cases hcase : Ω = ∅ ∨ N = 0
  · exact edge_cases hΩ X c g u hX hspan hc hEq hcase
  · have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · exact absurd (Or.inr h) hcase
      · exact h
    have hloc : ∀ x : Ω, ∃ U : Set (Fin N → ℝ), IsOpen U ∧ (x : Fin N → ℝ) ∈ U ∧ U ⊆ Ω ∧
        ∃ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧ f =ᵐ[volume.restrict U] u :=
      fun x => exists_local_representative hN hΩ X c g u hX hspan hc hE4 x.1 x.2 (hF4 hN x.1)
    choose U hUopen hxU hUsub f hf hae using hloc
    have hcover : ∀ x ∈ Ω, ∃ i : Ω, x ∈ U i := fun x hx => ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    have hchoice := patch_choice_smoothness hΩ U f u hUopen hUsub hcover hf hae
    refine ⟨patchChoice Ω U f hcover, hchoice.1, ?_⟩
    have hglue := countable_local_ae_gluing hΩ U f u hUopen hUsub hcover hf hae
    refine (ae_restrict_iff' hΩ.measurableSet).2 ?_
    filter_upwards [hglue] with x hx hxΩ
    exact (hx hxΩ).symm

end Hormander.F

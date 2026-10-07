-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ExactTimedFactorization
public import RothschildStein.G3.UniformScaledTimedError
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G3

/-- A uniform retained schedule estimate gives the actual fixed-length primitive
approximation, with coefficients independent of the initial point. -/
theorem exactTimedApproximation_of_schedule_error {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {R A η M : ℝ}
    (hfactor : ∀ f : formalSpan a s p, ‖f‖ ≤ R →
      ∃ S : List (Fin a × ℝ),
        S.length = enumeratedPrimitiveArcCount a s p ∧
        (∀ b ∈ S, |b.2| ≤ A) ∧ retainedLieListProduct (S.map (timedPrimitiveLieInput (s := s) (p := p))) = f)
    (K Ω : Set (Fin N → ℝ))
    (Ψ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (H : ((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ))
    (herror : ∀ S : List (Fin a × ℝ),
      S.length ≤ enumeratedPrimitiveArcCount a s p →
      (∀ b ∈ S, |b.2| ≤ A) → ‖retainedLieListProduct (S.map (timedPrimitiveLieInput (s := s) (p := p)))‖ ≤ R →
      ∀ x ∈ K, ∀ t : ℝ, |t| < η →
        TimedScheduleInside Ψ Ω (scaleTimedPrimitiveSchedule p t S) x ∧
        ‖runTimedPrimitiveSchedule Ψ (scaleTimedPrimitiveSchedule p t S) x -
          H (dilatedInputCoordinates D (retainedLieListProduct (S.map (timedPrimitiveLieInput (s := s) (p := p)))) t,x)‖ ≤
          M*|t| ^(s+1)) :
    ∀ f : formalSpan a s p, ‖f‖ ≤ R → ∃ S : List (Fin a × ℝ),
      S.length = enumeratedPrimitiveArcCount a s p ∧
      ∀ t : ℝ, |t| < η →
        (scaleTimedPrimitiveSchedule p t S).length = enumeratedPrimitiveArcCount a s p ∧
        (∀ b ∈ scaleTimedPrimitiveSchedule p t S, |b.2| ≤ A*|t| ^(p b.1 : ℕ)) ∧
        ∀ x ∈ K, TimedScheduleInside Ψ Ω (scaleTimedPrimitiveSchedule p t S) x ∧
          ‖runTimedPrimitiveSchedule Ψ (scaleTimedPrimitiveSchedule p t S) x -
            H (dilatedInputCoordinates D f t,x)‖ ≤ M*|t| ^(s+1) := by
  intro f hf
  obtain ⟨S,hlen,htime,hprod⟩ := hfactor f hf
  refine ⟨S,hlen,?_⟩
  intro t ht
  refine ⟨by simpa only [scaleTimedPrimitiveSchedule_length] using hlen,
    scaleTimedPrimitiveSchedule_time_bound p t S htime,?_⟩
  intro x hx
  have he := herror S hlen.le htime (by rw [hprod]; exact hf) x hx t ht
  simpa only [hprod] using he
end RothschildStein.G3

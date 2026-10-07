-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EnumeratedArcCount
public import RothschildStein.G3.TimedRootFactorProducts
public import RothschildStein.G3.RootScheduleTimeBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Bounded formal targets have fixed-length real primitive schedules with
one numerical bound on all normalized times. -/
theorem exists_bounded_exact_timed_factorization {a s : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) (hp : ∀ i, (p i : ℕ) ≤ s) (i₀ : Fin a) (R : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : formalSpan a s p, ‖f‖ ≤ R →
      ∃ S : List (Fin a × ℝ),
        S.length = enumeratedPrimitiveArcCount a s p ∧
        (∀ b ∈ S, |b.2| ≤ A) ∧
        retainedLieListProduct (S.map (timedPrimitiveLieInput (s := s) (p := p))) = f := by
  obtain ⟨B,hB,hfactor⟩ := exists_bounded_enumerated_quasi_factorization (p := p) hs R
  refine ⟨(max 1 B)^s,by positivity,?_⟩
  intro f hf
  obtain ⟨AS,hlen,hwords,hAS,hprod⟩ := hfactor f.val f.property hf
  let L := enumeratedPrimitiveArcCount a s p
  have hlenS : (rootTimedFactorSchedule p AS).length ≤ L := by
    change (rootTimedFactorSchedule p AS).length ≤ enumeratedPrimitiveArcCount a s p
    rw [rootTimedFactorSchedule_length,signedCorrectionArcSchedule_length_of_enumeration AS hwords]
  refine ⟨padTimedPrimitiveSchedule i₀ L (rootTimedFactorSchedule p AS),
    padTimedPrimitiveSchedule_length i₀ _ hlenS,?_,?_⟩
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · have he := rootTimedFactorSchedule_time_bound p AS hB.le (by norm_num : (0 : ℝ) ≤ 1)
        (fun b hb => ⟨(hAS b hb).1,by simpa using (hAS b hb).2.2⟩) b hb
      have he' : |b.2| ≤ (max 1 B)^(p b.1 : ℕ) := by simpa using he
      exact he'.trans (pow_le_pow_right₀ (le_max_left 1 B) (hp b.1))
    · have he := List.eq_of_mem_replicate hb
      subst b
      simp
  · rw [paddedTimedSchedule_retainedLieProduct,rootTimedFactorSchedule_retainedLieProduct]
    apply Subtype.ext
    exact hprod.symm
end RothschildStein.G3

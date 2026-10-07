-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffFirstSecondFamily
public import RothschildStein.H3.CompactQuasiballCutoff
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Every word of the constructed cutoff is globally smooth. -/
theorem smoothQuasiballCutoff_word_contDiff (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (I : List (Fin (q+1)))
    (x₀ : Fin N → ℝ) {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    ContDiff ℝ (⊤ : ℕ∞) (wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ t s)) :=
  contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) I _
    (smoothQuasiballCutoff_contDiff G ν hν x₀ ht hts).contDiffOn)

/-- The pointwise cutoff word bounds are genuine L-infinity bounds,
for arbitrary measures on the group, with measurability discharged. -/
theorem cutoff_word_eLpNorm_top_le_of_bound (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (I : List (Fin (q+1)))
    (x₀ : Fin N → ℝ) {t s C : ℝ} (ht : 0 < t) (hts : t < s)
    (μ : Measure (Fin N → ℝ))
    (hb : ∀ x, |wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ t s) x| ≤ C) :
    eLpNorm (wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ t s)) ⊤ μ ≤ ENNReal.ofReal C := by
  have hc := (smoothQuasiballCutoff_word_contDiff G H ν hν I x₀ ht hts).continuous
  rw [eLpNorm_exponent_top hc.aestronglyMeasurable]
  apply eLpNormEssSup_le_of_ae_bound
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x

/-- Uniform L-infinity constants for all horizontal first derivatives,
all ordered second horizontal derivatives, and the drift. -/
theorem exists_cutoff_first_second_Linfinity (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ x₀ : Fin N → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
        (∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ)
          (smoothQuasiballCutoff G ν x₀ t s)) ⊤ volume ≤ ENNReal.ofReal (c₁ / (s-t))) ∧
        (eLpNorm (fieldDerivative (H.fields 0) (smoothQuasiballCutoff G ν x₀ t s)) ⊤ volume ≤
          ENNReal.ofReal (c₂ / (s-t)^2)) ∧
        (∀ i j : Fin q, eLpNorm (fieldDerivative (H.fields i.succ)
          (fieldDerivative (H.fields j.succ) (smoothQuasiballCutoff G ν x₀ t s))) ⊤ volume ≤
            ENNReal.ofReal (c₂ / (s-t)^2)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hb⟩ := exists_cutoff_first_second_constants G H ν hν
  refine ⟨c₁, c₂, hc₁, hc₂, ?_⟩
  intro x₀ t s ht hts hhalf
  obtain ⟨hfirst, hdrift, hsecond⟩ := hb x₀ t s ht hts hhalf
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact cutoff_word_eLpNorm_top_le_of_bound G H ν hν [i.succ] x₀ ht hts volume (hfirst i)
  · exact cutoff_word_eLpNorm_top_le_of_bound G H ν hν [0] x₀ ht hts volume hdrift
  · intro i j
    exact cutoff_word_eLpNorm_top_le_of_bound G H ν hν [i.succ,j.succ] x₀ ht hts volume (hsecond i j)

end RothschildStein.H3

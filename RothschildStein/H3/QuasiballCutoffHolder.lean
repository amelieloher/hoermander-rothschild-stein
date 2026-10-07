-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ScaledControlHolder
public import RothschildStein.H3.CutoffAllWords
public import RothschildStein.H3.CutoffWordLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The smooth quasi-ball cutoff has its full
Hölder bound for every fixed ordered word, including the empty word.
Constants are chosen before the center and radii; the derivative budget
is not suppressed. BB Lemma 8.54, p. 384, corrected scale powers. -/
theorem exists_quasiball_cutoff_word_holder_constants {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) :
    ∃ C : List (Fin (q + 1)) → ℝ, (∀ I, 0 < C I) ∧
      ∀ I (x₀ : Fin N → ℝ) (t s : ℝ), 0 < t → t < s → s / 2 ≤ t →
      let metric : MetricSpace (ControlCarrier N) := gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ
        (wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ t s)) ≤
      ENNReal.ofReal (C I / (s - t) ^ H1.differentialWordWeight I *
        (1 + 2 / (s - t) ^ (α : ℝ))) := by
  classical
  obtain ⟨B, hB, hb⟩ := exists_cutoff_all_word_constants G H ν hν
  let C := fun I : List (Fin (q + 1)) =>
    (if I = [] then 1 else B I) + (∑ i : Fin q, B (i.succ :: I)) + B (0 :: I) + 1
  have hbase (I : List (Fin (q + 1))) : 0 ≤ (if I = [] then 1 else B I) := by
    split_ifs
    · norm_num
    · exact (hB I).le
  have hsum (I : List (Fin (q + 1))) : 0 ≤ ∑ i : Fin q, B (i.succ :: I) :=
    Finset.sum_nonneg (fun i _ => (hB _).le)
  have hC (I : List (Fin (q + 1))) : 0 < C I := by
    dsimp [C]
    linarith [hbase I, hsum I, hB (0 :: I)]
  refine ⟨C, hC, ?_⟩
  intro I x₀ t s ht hts hhalf
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  let a := s - t
  let k := H1.differentialWordWeight I
  let f := wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ t s)
  have ha : 0 < a := sub_pos.mpr hts
  have hsup : ∀ x, |f x| ≤ C I / a ^ k := by
    intro x
    by_cases hI : I = []
    · subst I
      have hr := smoothQuasiballCutoff_range G ν x₀ x t s
      have hc : 1 ≤ C [] := by dsimp [C]; linarith [hsum [], hB [0]]
      simpa only [f, wordDerivative, k, H1.differentialWordWeight, List.map_nil,
        List.sum_nil, pow_zero, div_one] using
        (show |smoothQuasiballCutoff G ν x₀ t s x| ≤ C [] from
          (by rw [abs_of_nonneg hr.1]; exact hr.2.trans hc))
    · have hBC : B I ≤ C I := by dsimp [C]; rw [ite_eq_right hI]; linarith [hsum I, hB (0 :: I)]
      exact (hb I hI x₀ t s ht hts hhalf x).trans
        (div_le_div_of_nonneg_right hBC (pow_nonneg ha.le k))
  have hfirst : ∀ x, ∀ i : Fin q,
      |fderiv ℝ f x (H.fields i.succ x)| ≤ B (i.succ :: I) / a ^ (k + 1) := by
    intro x i
    have hh := hb (i.succ :: I) (by simp) x₀ t s ht hts hhalf x
    simpa [H1.differentialWordWeight, Nat.add_comm, f, wordDerivative, fieldDerivative, k, a] using hh
  have hdrift : ∀ x, |fderiv ℝ f x (H.fields 0 x)| ≤ B (0 :: I) / a ^ (k + 2) := by
    intro x
    have hh := hb (0 :: I) (by simp) x₀ t s ht hts hhalf x
    simpa [H1.differentialWordWeight, Nat.add_comm, f, wordDerivative, fieldDerivative, k, a] using hh
  have hsumC : (∑ i : Fin q, B (i.succ :: I)) ≤ C I := by
    dsimp [C]; linarith [hbase I, hB (0 :: I)]
  have hzeroC : B (0 :: I) ≤ C I := by dsimp [C]; linarith [hbase I, hsum I]
  have hfirstC : (∑ i : Fin q, B (i.succ :: I) / a ^ (k + 1)) ≤ (C I / a ^ k) / a := by
    rw [← Finset.sum_div, pow_succ, div_div]
    exact div_le_div_of_nonneg_right hsumC (by positivity)
  have hdriftC : B (0 :: I) / a ^ (k + 2) ≤ (C I / a ^ k) / a ^ 2 := by
    rw [pow_add, div_div]
    exact div_le_div_of_nonneg_right hzeroC (by positivity)
  have hf := smoothQuasiballCutoff_word_contDiff G H ν hν I x₀ ht hts
  have hn := scaled_control_holderNorm_of_controlNorm Hc (hf.of_le (by simp)) ha
    (div_nonneg (hC I).le (pow_nonneg ha.le k)) hsup hfirst hdrift hfirstC hdriftC hα1
  have he : C I / a ^ k + 2 * (C I / a ^ k) / a ^ (α : ℝ) =
      C I / a ^ k * (1 + 2 / a ^ (α : ℝ)) := by ring
  rw [he] at hn
  exact hn

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffHolderPower
public import RothschildStein.H3.LocalSecondHolderLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The actual cutoff source coefficients have one uniform
zeroth-order loss and one uniform second-order loss. The horizontal
cross coefficients include their factor two. -/
theorem exists_quasiball_source_holder_coefficients {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {a : ℝ≥0} (ha1 : (a : ℝ) ≤ 1) {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let metric := gaugeMetric G C.norm C.constant_one C.symmetric
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ z : Fin N → ℝ, ∀ t s : ℝ,
      0 < t → t < s → s / 2 ≤ t → s - t ≤ Rmax →
      let φ := smoothQuasiballCutoff G ν z t s
      let normG := fun f : (Fin N → ℝ) → ℝ =>
        @H2.boundedHolderNorm (ControlCarrier N) metric a univ f
      normG φ ≤ ENNReal.ofReal (A * (s - t) ^ (-(a : ℝ))) ∧
      2 * (∑ i : Fin q, normG (wordDerivative H.fields [i.succ] φ)) +
        normG (wordDerivative H.fields [0] φ) +
        (∑ i : Fin q, normG (wordDerivative H.fields [i.succ, i.succ] φ)) ≤
        ENNReal.ofReal (B * (s - t) ^ (-(2 + (a : ℝ)))) := by
  classical
  let metric := gaugeMetric G C.norm C.constant_one C.symmetric
  dsimp only
  obtain ⟨c, hc, hb⟩ := exists_quasiball_cutoff_word_holder_power_constants G H C ν hν ha1 hRmax
  let B := 2 * Rmax * (∑ i : Fin q, c [i.succ]) + c [0] + ∑ i : Fin q, c [i.succ, i.succ]
  have hsum : 0 ≤ ∑ i : Fin q, c [i.succ] := Finset.sum_nonneg fun i _ => (hc _).le
  have hdiag : 0 ≤ ∑ i : Fin q, c [i.succ, i.succ] := Finset.sum_nonneg fun i _ => (hc _).le
  refine ⟨c [], B, hc [], by dsimp [B]; nlinarith [hc [0]], ?_⟩
  intro z t s ht hts hhalf hgap
  let d := s - t
  have hd : 0 < d := sub_pos.mpr hts
  let φ := smoothQuasiballCutoff G ν z t s
  let normG := fun f : (Fin N → ℝ) → ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric a univ f
  have hbound (I : List (Fin (q + 1))) : normG (wordDerivative H.fields I φ) ≤
      ENNReal.ofReal (c I * d ^ (-((H1.differentialWordWeight I : ℝ) + (a : ℝ)))) := by
    have hh := hb I z t s ht hts hhalf hgap
    simpa only [div_eq_mul_inv, Real.rpow_neg hd.le] using hh
  have hzero := hbound []
  have hpow : d ^ (-(1 + (a : ℝ))) ≤ Rmax * d ^ (-(2 + (a : ℝ))) := by
    have hh := bounded_gap_rpow_loss (a := 1 + (a : ℝ)) (b := 2 + (a : ℝ)) hd hgap (by linarith)
    simpa only [show 2 + (a : ℝ) - (1 + (a : ℝ)) = 1 by ring, Real.rpow_one] using hh
  have hfirst (i : Fin q) : normG (wordDerivative H.fields [i.succ] φ) ≤
      ENNReal.ofReal (Rmax * c [i.succ] * d ^ (-(2 + (a : ℝ)))) := by
    have hh := hbound [i.succ]
    simp only [H1.differentialWordWeight, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Fin.succ_ne_zero, ite_false, add_zero, Nat.cast_one] at hh
    apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_le_mul_of_nonneg_left hpow (hc [i.succ]).le]
  have hdrift : normG (wordDerivative H.fields [0] φ) ≤
      ENNReal.ofReal (c [0] * d ^ (-(2 + (a : ℝ)))) := by
    simpa only [H1.differentialWordWeight, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ite_true, add_zero, Nat.cast_ofNat] using hbound [0]
  have hsecond (i : Fin q) : normG (wordDerivative H.fields [i.succ, i.succ] φ) ≤
      ENNReal.ofReal (c [i.succ, i.succ] * d ^ (-(2 + (a : ℝ)))) := by
    simpa only [H1.differentialWordWeight, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Fin.succ_ne_zero, ite_false, add_zero, show (1 + 1 : ℕ) = 2 by norm_num, Nat.cast_ofNat] using hbound [i.succ, i.succ]
  refine ⟨?_, ?_⟩
  · simpa only [H1.differentialWordWeight, List.map_nil, List.sum_nil, Nat.cast_zero,
      zero_add, wordDerivative] using hzero
  · have h : 2 * (∑ i : Fin q, normG (wordDerivative H.fields [i.succ] φ)) +
        normG (wordDerivative H.fields [0] φ) +
        (∑ i : Fin q, normG (wordDerivative H.fields [i.succ, i.succ] φ)) ≤
        2 * (∑ i : Fin q, ENNReal.ofReal (Rmax * c [i.succ] * d ^ (-(2 + (a : ℝ))))) +
        ENNReal.ofReal (c [0] * d ^ (-(2 + (a : ℝ)))) +
        (∑ i : Fin q, ENNReal.ofReal (c [i.succ, i.succ] * d ^ (-(2 + (a : ℝ))))) := add_le_add (add_le_add (mul_le_mul' le_rfl
      (Finset.sum_le_sum fun i _ => hfirst i)) hdrift)
      (Finset.sum_le_sum fun i _ => hsecond i)
    apply h.trans_eq
    have hp : 0 ≤ d ^ (-(2 + (a : ℝ))) := Real.rpow_nonneg hd.le _
    have hn₁ (i : Fin q) : 0 ≤ Rmax * c [i.succ] * d ^ (-(2 + (a : ℝ))) :=
      mul_nonneg (mul_nonneg hRmax.le (hc _).le) hp
    have hn₂ (i : Fin q) : 0 ≤ c [i.succ, i.succ] * d ^ (-(2 + (a : ℝ))) :=
      mul_nonneg (hc _).le hp
    have hn₀ : 0 ≤ c [0] * d ^ (-(2 + (a : ℝ))) := mul_nonneg (hc _).le hp
    have hs₁ := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hn₁ i)
    have hs₂ := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hn₂ i)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hn₁ i),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hn₂ i)]
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hs₁) hn₀,
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by norm_num) hs₁) hn₀) hs₂]
    congr 1
    dsimp [B, d]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

end RothschildStein.H3

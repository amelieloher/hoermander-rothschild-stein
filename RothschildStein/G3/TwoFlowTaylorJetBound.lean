-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TwoFlowTaylorExpansion
public import RothschildStein.G3.MixedFieldPowerBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Uniform finite jet bounds give an explicit order-s+1 remainder
for the actual rectangular two-flow Taylor polynomial. The ordinary
coefficient-jet budget is 2s+1 (BB Lemma 9.22, pp. 413–414). -/
theorem two_integralCurves_taylor_bound_of_small_jets {N R s : ℕ}
    (Ω : Opens (Fin N → ℝ)) (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    {a b c d δ B F : ℝ} (α β : ℝ → (Fin N → ℝ))
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (U (α t)) t)
    (hαmem : ∀ t ∈ Ioo a b, α t ∈ Ω)
    (hβ : ∀ t ∈ Ioo c d, HasDerivAt β (V (β t)) t)
    (hβmem : ∀ t ∈ Ioo c d, β t ∈ Ω) (hβ₀ : β 0 = α 1)
    (hαseg : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo a b)
    (hβseg : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo c d)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hs : 2 * s + 1 ≤ R) (hB : 0 ≤ B) (hδ : |δ| ≤ 1)
    (hUjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j U (α t)‖ ≤ |δ| * B)
    (hVαjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j V (α t)‖ ≤ |δ| * B)
    (hVβjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j V (β t)‖ ≤ |δ| * B)
    (hfαjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j f (α t)‖ ≤ F)
    (hfβjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j f (β t)‖ ≤ F) :
    ‖f (β 1) - ∑ k ∈ Finset.range (s + 1), (k.factorial : ℝ)⁻¹ *
      (∑ j ∈ Finset.range (s + 1), (j.factorial : ℝ)⁻¹ *
        fieldPower U j (fieldPower V k f) (α 0))‖ ≤
      |δ| ^ (s + 1) * (((2 ^ R * B) ^ (s + 1) * F) +
        ∑ k ∈ Finset.range (s + 1), |(k.factorial : ℝ)⁻¹| * ((2 ^ R * B) ^ (s + 1 + k) * F)) := by
  have hF : 0 ≤ F := (norm_nonneg _).trans (hfαjet 0 (by simp) 0 (Nat.zero_le R))
  have hb : 0 ≤ |δ| * B := mul_nonneg (abs_nonneg δ) hB
  have hY : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fieldPower V (s + 1) f (β t)‖ ≤ (2 ^ R * (|δ| * B)) ^ (s + 1) * F := by
    intro t ht
    simpa only [norm_iteratedFDeriv_zero] using
      norm_fieldPower_jet_le Ω V hV f hf (hβmem t (hβseg t ht))
        (hVβjet t ht) (hfβjet t ht) (s + 1) 0 (by omega)
  have hX : ∀ k ∈ Finset.range (s + 1), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fieldPower U (s + 1) (fieldPower V k f) (α t)‖ ≤
        (2 ^ R * (|δ| * B)) ^ (s + 1 + k) * F := by
    intro k hk t ht
    have hk' := Finset.mem_range.mp hk
    simpa only [norm_iteratedFDeriv_zero] using
      norm_mixed_fieldPower_jet_le Ω U V hU hV f hf (hαmem t (hαseg t ht)) hb
        (hUjet t ht) (hVαjet t ht) (hfαjet t ht) (s + 1) k 0 (by omega)
  have hh := two_integralCurves_pullback_taylor_bound Ω U V hU hV α β hα hαmem hβ hβmem
    hβ₀ (σ := 1) (τ := 1) (by simpa only [mul_one] using hαseg)
    (by simpa only [mul_one] using hβseg) f hf s s
    ((2 ^ R * (|δ| * B)) ^ (s + 1) * F)
    (fun k => (2 ^ R * (|δ| * B)) ^ (s + 1 + k) * F)
    (by simpa only [mul_one] using hY) (by simpa only [mul_one] using hX)
  simp only [one_pow, one_div, abs_one, mul_one] at hh
  apply hh.trans
  have hp : ∀ n, s + 1 ≤ n →
      (2 ^ R * (|δ| * B)) ^ n * F ≤ |δ| ^ (s + 1) * ((2 ^ R * B) ^ n * F) := by
    intro n hn
    calc
      _ = |δ| ^ n * ((2 ^ R * B) ^ n * F) := by rw [mul_left_comm, mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (abs_nonneg δ) hδ hn)
        (mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hB) _) hF)
  rw [mul_add, Finset.mul_sum]
  apply add_le_add (hp (s + 1) le_rfl)
  apply Finset.sum_le_sum
  intro k _
  exact (mul_le_mul_of_nonneg_left (hp (s + 1 + k) (by omega)) (abs_nonneg _)).trans_eq (by ring)
end RothschildStein.G3

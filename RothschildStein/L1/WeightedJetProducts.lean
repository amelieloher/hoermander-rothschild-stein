-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JetLeibnizFormula
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Weighted thresholds add under multiplication. -/
theorem scalarJetVanishing_mul {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {f g : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    (hfa : scalarJetVanishing ω a p f) (hgb : scalarJetVanishing ω b p g) :
    scalarJetVanishing ω (a+b) p (fun u => f u * g u) := by
  intro J hJ hw
  rw [rsPartial_mul_eq_leibniz Ω f g hf hg J 0 h0]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hl, hwq⟩ := jetLeibnizPartitions_order_weight ω J q hq
  have hreal : (((q.1.map ω).sum : ℕ) : ℝ) +
      (((q.2.map ω).sum : ℕ) : ℝ) = (((J.map ω).sum : ℕ) : ℝ) := by
    exact_mod_cast hwq
  by_cases hwa : (((q.1.map ω).sum : ℕ) : ℝ) < a
  · rw [hfa q.1 (by omega) hwa, zero_mul]
  · rw [hgb q.2 (by omega) (by linarith), mul_zero]

/-- The smooth jet classes are closed under multiplication with added thresholds. -/
theorem scalarJetClass_mul {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {f g : (Fin N → ℝ) → ℝ} (hf : scalarJetClass Ω ω a p f)
    (hg : scalarJetClass Ω ω b p g) :
    scalarJetClass Ω ω (a+b) p (fun u => f u * g u) :=
  ⟨hf.1.mul hg.1, scalarJetVanishing_mul Ω h0 hf.1 hg.1 hf.2 hg.2⟩

/-- A factor vanishing at zero saves one ordinary
jet order in the other factor. This is valid also at p = 0. -/
theorem scalarJetVanishing_mul_of_zero {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {f g : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) (hf0 : f 0 = 0)
    (hfa : scalarJetVanishing ω a (p+1) f) (hgb : scalarJetVanishing ω b p g) :
    scalarJetVanishing ω (a+b) (p+1) (fun u => f u * g u) := by
  intro J hJ hw
  rw [rsPartial_mul_eq_leibniz Ω f g hf hg J 0 h0]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hl, hwq⟩ := jetLeibnizPartitions_order_weight ω J q hq
  by_cases he : q.1 = []
  · simp only [he, rsPartial, hf0, zero_mul]
  · have hpos : 0 < q.1.length := List.length_pos_iff.mpr he
    have hreal : (((q.1.map ω).sum : ℕ) : ℝ) +
        (((q.2.map ω).sum : ℕ) : ℝ) = (((J.map ω).sum : ℕ) : ℝ) := by
      exact_mod_cast hwq
    by_cases hwa : (((q.1.map ω).sum : ℕ) : ℝ) < a
    · rw [hfa q.1 (by omega) hwa, zero_mul]
    · rw [hgb q.2 (by omega) (by linarith), mul_zero]
end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FlowTaylorExpansion
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology BigOperators
namespace RothschildStein.G3

/-- Two successive flow pullbacks have an ordered rectangular Taylor
polynomial, with remainder controlled on the actual two trajectories
(BB (9.10), p. 411). The operator order is X followed by Y. -/
theorem two_integralCurves_pullback_taylor_bound {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (X Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω)
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω) {a b c d σ τ : ℝ}
    (α β : ℝ → (Fin N → ℝ))
    (hα : ∀ r ∈ Ioo a b, HasDerivAt α (X (α r)) r)
    (hαmem : ∀ r ∈ Ioo a b, α r ∈ Ω)
    (hβ : ∀ r ∈ Ioo c d, HasDerivAt β (Y (β r)) r)
    (hβmem : ∀ r ∈ Ioo c d, β r ∈ Ω) (hβ₀ : β 0 = α σ)
    (hσ : ∀ r ∈ Icc (0 : ℝ) 1, r * σ ∈ Ioo a b)
    (hτ : ∀ r ∈ Icc (0 : ℝ) 1, r * τ ∈ Ioo c d)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (m n : ℕ) (MY : ℝ) (MX : ℕ → ℝ)
    (hYbound : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖fieldPower Y (n + 1) f (β (r * τ))‖ ≤ MY)
    (hXbound : ∀ k ∈ Finset.range (n + 1), ∀ r ∈ Icc (0 : ℝ) 1,
      ‖fieldPower X (m + 1) (fieldPower Y k f) (α (r * σ))‖ ≤ MX k) :
    ‖f (β τ) - ∑ k ∈ Finset.range (n + 1),
      (τ ^ k / (k.factorial : ℝ)) *
        (∑ j ∈ Finset.range (m + 1),
          (σ ^ j / (j.factorial : ℝ)) * fieldPower X j (fieldPower Y k f) (α 0))‖ ≤
      MY * |τ| ^ (n + 1) +
        ∑ k ∈ Finset.range (n + 1),
          |τ ^ k / (k.factorial : ℝ)| * (MX k * |σ| ^ (m + 1)) := by
  let P (k : ℕ) := ∑ j ∈ Finset.range (m + 1),
    (σ ^ j / (j.factorial : ℝ)) * fieldPower X j (fieldPower Y k f) (α 0)
  let w (k : ℕ) := τ ^ k / (k.factorial : ℝ)
  have hy := integralCurve_pullback_taylor_bound Ω Y hY β hβ hβmem f hf n hτ hYbound
  rw [hβ₀] at hy
  have hx : ∀ k ∈ Finset.range (n + 1),
      ‖fieldPower Y k f (α σ) - P k‖ ≤ MX k * |σ| ^ (m + 1) := by
    intro k hk
    exact integralCurve_pullback_taylor_bound Ω X hX α hα hαmem _
      (contDiffOn_fieldPower Ω Y hY k f hf) m hσ (hXbound k hk)
  have hs : ‖(∑ k ∈ Finset.range (n + 1), w k * fieldPower Y k f (α σ)) -
      ∑ k ∈ Finset.range (n + 1), w k * P k‖ ≤
      ∑ k ∈ Finset.range (n + 1), |w k| * (MX k * |σ| ^ (m + 1)) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ‖∑ k ∈ Finset.range (n + 1), w k * (fieldPower Y k f (α σ) - P k)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ ∑ k ∈ Finset.range (n + 1), ‖w k * (fieldPower Y k f (α σ) - P k)‖ :=
        norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hx k hk) (abs_nonneg _)
  exact (norm_sub_le_norm_sub_add_norm_sub (f (β τ))
    (∑ k ∈ Finset.range (n + 1), w k * fieldPower Y k f (α σ))
    (∑ k ∈ Finset.range (n + 1), w k * P k)).trans (add_le_add hy hs)
end RothschildStein.G3

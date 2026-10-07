-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PhiAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
open scoped ENNReal

/-- The common coefficient in the explicit cutoff expansion. -/
def cutoffInterpolationConstant (q c₁ c₂ : ℝ) : ℝ :=
  max (4 * c₁) (max (4 * q * c₂) (2 * q))

/-- Converting the first and second cutoff coefficients into a common
coefficient for the interpolation estimate. -/
theorem cutoffInterpolation_step {q c₁ c₂ w ε n n₀ n₁ n₂ : ℝ}
    (hw : 0 < w) (hε : 0 < ε) (hn₀ : 0 ≤ n₀) (hn₁ : 0 ≤ n₁)
    (h : n ≤ ε * (n₂ + (4 * c₁ / w) * n₁ +
      (4 * q * c₂ / w^2) * n₀) + (2 * q / ε) * n₀) :
    n ≤ ε * (n₂ + (cutoffInterpolationConstant q c₁ c₂ / w) * n₁ +
      (cutoffInterpolationConstant q c₁ c₂ / w^2) * n₀) +
      (cutoffInterpolationConstant q c₁ c₂ / ε) * n₀ := by
  have h₁ : 4 * c₁ ≤ cutoffInterpolationConstant q c₁ c₂ := le_max_left _ _
  have h₂ : 4 * q * c₂ ≤ cutoffInterpolationConstant q c₁ c₂ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hq' : 2 * q ≤ cutoffInterpolationConstant q c₁ c₂ :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact h.trans (by gcongr)

/-- Explicit geometric constants under the cutoff and flow hypotheses.
This is BB (8.53) after absorbing the cutoff error; the analytic estimate
is a separate premise. -/
theorem phi_interpolation_of_cutoff_step (I : Set ℝ) (N₀ N₁ N₂ : ℝ → ℝ)
    {r q c₁ c₂ : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hI : I = Ioo (1 / 2 : ℝ) 1 ∨ I = Ico (1 / 2 : ℝ) 1)
    (hfinite : phi I r 1 N₁ ≠ ⊤)
    (hN₀ : ∀ σ ∈ I, 0 ≤ N₀ σ) (hN₁ : ∀ σ ∈ I, 0 ≤ N₁ σ)
    (hstep : ∀ σ ∈ I, ∀ ε : ℝ, 0 < ε →
      N₁ σ ≤ ε * (N₂ ((1 + σ) / 2) +
        (4 * c₁ / ((1 - σ) * r)) * N₁ ((1 + σ) / 2) +
        (4 * q * c₂ / (((1 - σ) * r)^2)) * N₀ ((1 + σ) / 2)) +
        (2 * q / ε) * N₀ ((1 + σ) / 2)) :
    ∃ cE δE : ℝ, 0 < cE ∧ 0 < δE ∧
      cE = 32 * cutoffInterpolationConstant q c₁ c₂ ∧
      δE = min 8 (2 / cutoffInterpolationConstant q c₁ c₂) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δE →
        phi I r 1 N₁ ≤ ENNReal.ofReal δ * phi I r 2 N₂ +
          ENNReal.ofReal (cE / δ) * phi I r 0 N₀ := by
  let c := cutoffInterpolationConstant q c₁ c₂
  have hc : 0 < c := lt_of_lt_of_le (by positivity : 0 < 2 * q)
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨32*c, min 8 (2/c), by positivity, by positivity, rfl, rfl, ?_⟩
  intro δ hδ hδE
  obtain ⟨hsub, hnext⟩ := phi_interval_geometry hI
  have hsmall : δ * c ≤ 2 :=
    (le_div_iff₀ hc).mp (hδE.trans (min_le_right _ _))
  apply phi_absorption_normalized (ε₀ := ⊤) I N₀ N₁ N₂ hr hc hδ
    (hδE.trans (min_le_left _ _)) hsmall (by simp) hI hfinite
  intro σ hσ ε hε _
  have hw : 0 < (1 - σ) * r := mul_pos (sub_pos.mpr (hsub hσ).2) hr
  have hs := cutoffInterpolation_step hw hε
    (hN₀ _ (hnext σ hσ)) (hN₁ _ (hnext σ hσ)) (hstep σ hσ ε hε)
  simpa only [c, mul_pow] using hs

end RothschildStein.H3

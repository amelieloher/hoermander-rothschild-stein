-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
open scoped ENNReal

/-- The extended-valued weighted supremum used in BB 8.41. -/
def phi (I : Set ℝ) (r : ℝ) (k : ℕ) (N : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ σ ∈ I, ENNReal.ofReal ((1 - σ) ^ k * r ^ k * N σ)

/-- Finite scalar absorption with the explicit constants in the estimate
of BB Theorem 8.42, p. 371. -/
theorem phi_scalar_absorption {a b d c δ : ℝ}
    (ha : 0 ≤ a) (_hb : 0 ≤ b) (hd : 0 ≤ d) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsmall : 4 * δ * c ≤ 1)
    (h : a ≤ 4 * δ * b + 2 * δ * c * a + (δ * c + c / δ) * d) :
    a ≤ 8 * δ * b + (4 * c / δ) * d := by
  have hhalf : 2 * δ * c * a ≤ a / 2 := by nlinarith
  have hcoeff : δ * c ≤ c / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) (mul_nonneg hδ.le hc.le)]
  have hlast : (δ * c + c / δ) * d ≤ 2 * (c / δ) * d := by
    apply mul_le_mul_of_nonneg_right _ hd
    linarith
  rw [show 4 * c / δ = 4 * (c / δ) by ring]
  linarith only [h, hhalf, hlast]

/-- A single reweighted step. The bounds are the values of the three
finite Phi seminorms at sigma-prime; epsilon is delta (1-sigma) r. -/
theorem phi_reweighted_step {r c δ σ n₀ n₁ n₂ n : ℝ} {P₀ P₁ P₂ : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hδ : 0 < δ) (hσ : σ < 1)
    (h₀ : n₀ ≤ P₀)
    (h₁ : (1 - (1 + σ) / 2) * r * n₁ ≤ P₁)
    (h₂ : (1 - (1 + σ) / 2) ^ 2 * r ^ 2 * n₂ ≤ P₂)
    (h : n ≤ (δ * (1 - σ) * r) *
      (n₂ + c / ((1 - σ) * r) * n₁ +
        c / ((1 - σ) ^ 2 * r ^ 2) * n₀) +
      c / (δ * (1 - σ) * r) * n₀) :
    (1 - σ) * r * n ≤
      4 * δ * P₂ + 2 * δ * c * P₁ + (δ * c + c / δ) * P₀ := by
  have hw : 0 < (1 - σ) * r := mul_pos (sub_pos.mpr hσ) hr
  have hscaled := mul_le_mul_of_nonneg_left h hw.le
  have heq : (1 - σ) * r * ((δ * (1 - σ) * r) *
      (n₂ + c / ((1 - σ) * r) * n₁ +
        c / ((1 - σ) ^ 2 * r ^ 2) * n₀) +
      c / (δ * (1 - σ) * r) * n₀) =
      4 * δ * ((1 - (1 + σ) / 2) ^ 2 * r ^ 2 * n₂) +
      2 * δ * c * ((1 - (1 + σ) / 2) * r * n₁) +
      (δ * c + c / δ) * n₀ := by
    field_simp [hr.ne', hδ.ne', (sub_pos.mpr hσ).ne']
    ring
  rw [heq] at hscaled
  have h2 := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 4 * δ)
  have h1 := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 2 * δ * c)
  have h0 := mul_le_mul_of_nonneg_left h₀ (by positivity : 0 ≤ δ * c + c / δ)
  linarith

/-- The full extended-valued Phi absorption export. Both open and
half-closed intervals are covered. The epsilon cap may be infinite.
BB Theorems 8.42 and 11.39, pp. 371 and 583. -/
theorem phi_absorption (I : Set ℝ) (N₀ N₁ N₂ : ℝ → ℝ)
    {r c δ : ℝ} {ε₀ : ℝ≥0∞}
    (hr : 0 < r) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : 4 * δ * c ≤ 1)
    (hcap : ENNReal.ofReal (δ * r / 2) ≤ ε₀)
    (hI : I ⊆ Ico (1 / 2 : ℝ) 1)
    (hnext : ∀ σ ∈ I, (1 + σ) / 2 ∈ I)
    (hfinite : phi I r 1 N₁ ≠ ⊤)
    (hstep : ∀ σ ∈ I, ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ε ≤ ε₀ →
      N₁ σ ≤ ε * (N₂ ((1 + σ) / 2) +
        c / ((1 - σ) * r) * N₁ ((1 + σ) / 2) +
        c / ((1 - σ) ^ 2 * r ^ 2) * N₀ ((1 + σ) / 2)) +
        c / ε * N₀ ((1 + σ) / 2)) :
    phi I r 1 N₁ ≤ ENNReal.ofReal (8 * δ) * phi I r 2 N₂ +
      ENNReal.ofReal (4 * c / δ) * phi I r 0 N₀ := by
  by_cases h₀ : phi I r 0 N₀ = ⊤
  · rw [h₀, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity : 0 < 4 * c / δ)).ne']
    simp only [add_top, le_top]
  by_cases h₂ : phi I r 2 N₂ = ⊤
  · rw [h₂, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity : 0 < 8 * δ)).ne']
    simp only [top_add, le_top]
  let P₀ := (phi I r 0 N₀).toReal
  let P₁ := (phi I r 1 N₁).toReal
  let P₂ := (phi I r 2 N₂).toReal
  have hb (k : ℕ) (N : ℝ → ℝ) (hk : phi I r k N ≠ ⊤) (σ : ℝ) (hσ : σ ∈ I) :
      (1 - σ) ^ k * r ^ k * N σ ≤ (phi I r k N).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hk).mp
    exact le_iSup_of_le σ (le_iSup_of_le hσ le_rfl)
  have hpoint (σ : ℝ) (hσ : σ ∈ I) :
      (1 - σ) * r * N₁ σ ≤
        4 * δ * P₂ + 2 * δ * c * P₁ + (δ * c + c / δ) * P₀ := by
    have hs := hI hσ
    have hslo : (1 / 2 : ℝ) ≤ σ := hs.1
    have hshi : σ < 1 := hs.2
    have he : 0 < δ * (1 - σ) * r := by positivity
    have hecap : ENNReal.ofReal (δ * (1 - σ) * r) ≤ ε₀ := by
      apply le_trans (ENNReal.ofReal_le_ofReal ?_) hcap
      nlinarith [mul_pos hδ hr]
    apply phi_reweighted_step hr hc hδ hs.2
      (by simpa [P₀] using hb 0 N₀ h₀ _ (hnext σ hσ))
      (by simpa [P₁] using hb 1 N₁ hfinite _ (hnext σ hσ))
      (by simpa [P₂] using hb 2 N₂ h₂ _ (hnext σ hσ))
      (hstep σ hσ _ he hecap)
  have hsup : P₁ ≤ 4 * δ * P₂ + 2 * δ * c * P₁ + (δ * c + c / δ) * P₀ := by
    apply (ENNReal.le_ofReal_iff_toReal_le hfinite (by positivity)).mp
    apply iSup_le
    intro σ
    apply iSup_le
    intro hσ
    exact ENNReal.ofReal_le_ofReal (by simpa using hpoint σ hσ)
  have hresult := phi_scalar_absorption
    (ENNReal.toReal_nonneg : 0 ≤ P₁) (ENNReal.toReal_nonneg : 0 ≤ P₂)
    (ENNReal.toReal_nonneg : 0 ≤ P₀) hc hδ hδ1 hsmall hsup
  have hfinal := ENNReal.ofReal_le_ofReal hresult
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * δ),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * c / δ)] at hfinal
  simpa only [P₀, P₁, P₂, ENNReal.ofReal_toReal h₀,
    ENNReal.ofReal_toReal h₂, ENNReal.ofReal_toReal hfinite] using hfinal

/-- Both interval conventions in BB Chapters 8 and 11 satisfy the
midpoint closure and the radius bounds required by phi_absorption. -/
theorem phi_interval_geometry {I : Set ℝ}
    (hI : I = Ioo (1 / 2 : ℝ) 1 ∨ I = Ico (1 / 2 : ℝ) 1) :
    I ⊆ Ico (1 / 2 : ℝ) 1 ∧ ∀ σ ∈ I, (1 + σ) / 2 ∈ I := by
  rcases hI with rfl | rfl
  · constructor
    · intro σ hσ; exact ⟨hσ.1.le, hσ.2⟩
    · intro σ hσ
      constructor <;> linarith [hσ.1, hσ.2]
  · constructor
    · exact subset_rfl
    · intro σ hσ
      constructor <;> linarith [hσ.1, hσ.2]

/-- BB's normalized interpolation form, with coefficient eta in
front of Phi_2 and the explicit constant 32 c / eta. -/
theorem phi_absorption_normalized (I : Set ℝ) (N₀ N₁ N₂ : ℝ → ℝ)
    {r c η : ℝ} {ε₀ : ℝ≥0∞}
    (hr : 0 < r) (hc : 0 < c) (hη : 0 < η) (hη8 : η ≤ 8)
    (hsmall : η * c ≤ 2)
    (hcap : ENNReal.ofReal (η * r / 16) ≤ ε₀)
    (hI : I = Ioo (1 / 2 : ℝ) 1 ∨ I = Ico (1 / 2 : ℝ) 1)
    (hfinite : phi I r 1 N₁ ≠ ⊤)
    (hstep : ∀ σ ∈ I, ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ε ≤ ε₀ →
      N₁ σ ≤ ε * (N₂ ((1 + σ) / 2) +
        c / ((1 - σ) * r) * N₁ ((1 + σ) / 2) +
        c / ((1 - σ) ^ 2 * r ^ 2) * N₀ ((1 + σ) / 2)) +
        c / ε * N₀ ((1 + σ) / 2)) :
    phi I r 1 N₁ ≤ ENNReal.ofReal η * phi I r 2 N₂ +
      ENNReal.ofReal (32 * c / η) * phi I r 0 N₀ := by
  obtain ⟨hsub, hnext⟩ := phi_interval_geometry hI
  have h := phi_absorption I N₀ N₁ N₂ hr hc
    (show 0 < η / 8 by positivity) (show η / 8 ≤ 1 by linarith)
    (show 4 * (η / 8) * c ≤ 1 by nlinarith)
    (by rw [show η / 8 * r / 2 = η * r / 16 by ring]; exact hcap)
    hsub hnext hfinite hstep
  rw [show 8 * (η / 8) = η by ring,
    show 4 * c / (η / 8) = 32 * c / η by field_simp; ring] at h
  exact h

end RothschildStein.H3

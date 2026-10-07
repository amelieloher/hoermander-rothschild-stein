-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNoDriftStep
public import RothschildStein.P2.SobolevInterpolationAbsorb

/-!
# Sobolev interpolation without drift, seminorm absorption: `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀`

Abstract absorption argument of the Sobolev interpolation inequality (BB p. 583, Thm 11.39; its prototype is BB p. 371, Thm 8.42) for a
no-drift alphabet (`Fin q`, all weights one, `L̃ = sumSquares`), for a family `U` of nested open sets
(the `ρ`-balls) and cutoffs between `U_{σ r}` and `U_{σ' r}`, `σ' = (1 + σ)/2`, with the weighted
derivative bounds `|X̃_I φ| ≤ B (t - s)^{-|I|}`. The real and `ℝ≥0∞` arithmetic of
`SobolevInterpolationAbsorb` (`ennreal_absorb`, `step_scale`, `absorb_const_le`, …) is reused.

For `σ ∈ [1/2, 1)`, `h = (1 - σ') r = (t - s)`, apply `seminorm_step_noDrift` with `ε = τ h`:
`((1-σ) r) ∑_l ‖X̃_l u‖_{U_{σ r}} ≤ 2τ (h² ∑_{|I|=2} ‖X̃_I u‖_{U_{σ' r}}) + 4Bτ (h ∑_{|I|=1} ‖X̃_I u‖_{U_{σ'r}})
  + (2τ(q+1)B + 2Cp/τ) ‖u‖_{U_{σ'r}}`, hence `Φ₁ ≤ 2τ Φ₂ + 4Bτ Φ₁ + (2τ(q+1)B + 2Cp/τ) Φ₀`.
Since `Φ₁ < ∞` (`u ∈ W^{2,p}`), `4Bτ ≤ 1/2` gives the absorption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein

section MainNoDrift

variable {n q : ℕ} {w : Fin q → ℕ+} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}

/-- Every term of the supremum defining `seminormPhi` is at most `seminormPhi` (no-drift
alphabet). -/
theorem le_seminormPhi_noDrift (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (U : ℝ → Opens (Fin n → ℝ)) (p : ℝ≥0∞) (r : ℝ) (j : ℕ) (u : (Fin n → ℝ) → ℝ) {σ : ℝ}
    (hσ : σ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ENNReal.ofReal (((1 - σ) * r) ^ j) *
        ∑ I ∈ wordsOfWeight w j, weakWordENorm X (U (σ * r)) I p u ≤
      seminormPhi w X U p r j u :=
  le_iSup₂ (f := fun σ (_ : σ ∈ Set.Ico (1 / 2 : ℝ) 1) => ENNReal.ofReal (((1 - σ) * r) ^ j) *
    ∑ I ∈ wordsOfWeight w j, weakWordENorm X (U (σ * r)) I p u) σ hσ

/-- The cutoffs from the radial cutoff construction between `U_{σ r}` and `U_{σ' r}`, `σ' = (1 + σ)/2`, `σ ∈ [1/2, 1)`, in a
no-drift alphabet: `φ ∈ C_c^∞(U_r)` with `0 ≤ φ ≤ 1`, `φ = 1` on `U_{σ r}`, `tsupport φ ⊆ U_{σ' r}` and the
weighted derivative bounds `|X̃_I φ| ≤ B (t - s)^{-|I|}`, `t - s = (1 - σ') r`, for the words `[l]`
(weight one) and `[l, l]` (weight two). -/
def CutoffFamilyNoDrift (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (U : ℝ → Opens (Fin n → ℝ))
    (r B : ℝ) : Prop :=
  ∀ σ ∈ Set.Ico (1 / 2 : ℝ) 1, ∃ φ : TestFunction (U r) ℝ (⊤ : ℕ∞),
    (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x ∈ (U (σ * r) : Set (Fin n → ℝ)), φ x = 1) ∧
    tsupport (φ : (Fin n → ℝ) → ℝ) ⊆ (U (((1 + σ) / 2) * r) : Set (Fin n → ℝ)) ∧
    (∀ (l : Fin q) (x : Fin n → ℝ), |fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ) x| ≤
      B / ((1 - (1 + σ) / 2) * r)) ∧
    (∀ (l : Fin q) (x : Fin n → ℝ),
      |fieldDerivative (X l) (fieldDerivative (X l) (φ : (Fin n → ℝ) → ℝ)) x| ≤
        B / ((1 - (1 + σ) / 2) * r) ^ 2)

/-- **The absorption inequality, no drift** `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀`
(BB p. 583, Thm 11.39), for a nested family `U` of open sets with cutoffs (`CutoffFamilyNoDrift`), on which
the compact interpolation inequality `CompactInterpolationOnNoDrift` holds with constants `εs, Cp`:
for `0 < δ ≤ 1/2`, `δ < εs`, `0 < r ≤ 1` and `u ∈ W^{2,p}_{X̃}(U_r)`,
`Φ₁ ≤ δ Φ₂ + ((q + 1 + 16 Cp (1 + B))/δ) Φ₀`. -/
theorem seminormPhi_absorption_noDrift
    (hw : ∀ j, (w j : ℕ) = 1) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p εs Cp : ℝ} (hp : 1 < p) (hCp : 0 ≤ Cp)
    (hCI : CompactInterpolationOnNoDrift X V a p εs Cp) {U : ℝ → Opens (Fin n → ℝ)}
    (hmono : ∀ s t : ℝ, s ≤ t → U s ≤ U t) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hrV : U r ≤ V)
    (hra : ∀ x ∈ (U r : Set (Fin n → ℝ)), a x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hcut : CutoffFamilyNoDrift X U r B) {u : (Fin n → ℝ) → ℝ}
    (hu : memSobolevX w X (U r) 2 (ENNReal.ofReal p) u) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hδs : δ < εs) :
    seminormPhi w X U (ENNReal.ofReal p) r 1 u ≤
      ENNReal.ofReal δ * seminormPhi w X U (ENNReal.ofReal p) r 2 u +
        ENNReal.ofReal (((q : ℝ) + 1 + 16 * Cp * (1 + B)) / δ) *
          seminormPhi w X U (ENNReal.ofReal p) r 0 u := by
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  set Φ₀ := seminormPhi w X U P r 0 u with hΦ₀
  set Φ₁ := seminormPhi w X U P r 1 u with hΦ₁
  set Φ₂ := seminormPhi w X U P r 2 u with hΦ₂
  set τ : ℝ := δ / (4 * (1 + B)) with hτ
  have hB1 : 0 < 1 + B := by linarith
  have hτ0 : 0 < τ := by positivity
  have hτδ : 4 * τ ≤ δ := four_tau_le hδ hB
  have hτs : τ < εs := by linarith
  -- the weak derivatives of `u` and the finiteness of `Φ₁`
  have hmem1 : ∀ l : Fin q, [l] ∈ wordFamily w 2 := fun l => by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw l]
  choose g1 hg1 using fun l : Fin q => hu.2 [l] (hmem1 l)
  have hΩ'U : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 → U (σ * r) ≤ U r := fun σ hσ =>
    hmono _ _ (by nlinarith [hσ.1, hσ.2])
  have hfin : Φ₁ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal r * ∑ l : Fin q,
      eLpNorm (g1 l) P (volume.restrict (U r : Set (Fin n → ℝ)))) ?_ ?_
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.sum_ne_top.2 fun l _ => (hg1 l).2.eLpNorm_ne_top)
    · rw [hΦ₁]
      unfold seminormPhi
      refine iSup₂_le fun σ hσ => ?_
      rw [sum_wordsOfWeight_one_noDrift hw, pow_one]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith [hσ.1, hσ.2])) ?_
      refine Finset.sum_le_sum fun l _ => ?_
      rw [S.weakWordENorm_eq X (U (σ * r)) _ P u _
        (S.hasWeakWordDeriv_restrict X (U r) _ (hΩ'U σ hσ) (hg1 l).1)]
      exact eLpNorm_mono_measure _ (Measure.restrict_mono (hΩ'U σ hσ) le_rfl)
  -- the inequality for each `σ`
  have hσ : ∀ σ ∈ Set.Ico (1 / 2 : ℝ) 1,
      ENNReal.ofReal (((1 - σ) * r) ^ 1) *
          ∑ I ∈ wordsOfWeight w 1, weakWordENorm X (U (σ * r)) I P u ≤
        ENNReal.ofReal (2 * τ) * Φ₂ + ENNReal.ofReal (4 * B * τ) * Φ₁ +
          ENNReal.ofReal (2 * τ * ((q : ℝ) + 1) * B + 2 * Cp / τ) * Φ₀ := by
    intro σ hσ
    obtain ⟨φ, hφ0, hφ1, hφs, hφt, hb1, hb2⟩ := hcut σ hσ
    set σ' : ℝ := (1 + σ) / 2 with hσ'
    have hσ'mem : σ' ∈ Set.Ico (1 / 2 : ℝ) 1 := ⟨by rw [hσ']; linarith [hσ.1],
      by rw [hσ']; linarith [hσ.2]⟩
    set h : ℝ := (1 - σ') * r with hh
    have hh0 : 0 < h := mul_pos (by linarith [hσ'mem.2]) hr0
    have hh1 : h ≤ 1 := by
      have : 1 - σ' ≤ 1 := by linarith [hσ'mem.1]
      nlinarith
    have hUs : U (σ * r) ≤ U (σ' * r) := hmono _ _ (mul_le_mul_of_nonneg_right
      (by rw [hσ']; linarith [hσ.2]) hr0.le)
    have hUt : U (σ' * r) ≤ U r := hΩ'U σ' hσ'mem
    have hstep := seminorm_step_noDrift hw hXV hp hCI (Ω' := U r) (Us := U (σ * r))
      (Ut := U (σ' * r)) hrV hra hUs hUt hu φ hφ0 hφ1 hφs hφt (b1 := B / h) (b2 := B / h ^ 2)
      (by positivity) (by positivity) hb1 hb2 (ε := τ * h) (by positivity)
      (by nlinarith)
    have hstep' : (∑ l : Fin q, weakWordENorm X (U (σ * r)) [l] P u) ≤
        ENNReal.ofReal (τ * h) * ((∑ l : Fin q, weakWordENorm X (U (σ' * r)) [l, l] P u) +
          ENNReal.ofReal (2 * (B / h)) * ∑ l : Fin q, weakWordENorm X (U (σ' * r)) [l] P u +
          ((q : ℝ≥0∞) + 1) * ENNReal.ofReal (B / h ^ 2) * weakWordENorm X (U (σ' * r)) [] P u) +
        ENNReal.ofReal (Cp / (τ * h)) * weakWordENorm X (U (σ' * r)) [] P u :=
      hstep.trans (add_le_add (mul_le_mul' le_rfl (add_le_add le_rfl
        (mul_le_mul' (mul_le_mul' le_self_add le_rfl) le_rfl))) le_rfl)
    have hscale := step_scale (q := q) hh0 hτ0 hB hCp hstep'
    have hlhs : (1 - σ) * r = 2 * h := by rw [hh, hσ']; ring
    -- the three terms on the right
    have e2 : ENNReal.ofReal (h ^ 2) *
        (∑ l : Fin q, weakWordENorm X (U (σ' * r)) [l, l] P u) ≤ Φ₂ :=
      (mul_le_mul' le_rfl (sum_wordsOfWeight_two_ge_noDrift hw _)).trans
        (le_seminormPhi_noDrift X U P r 2 u hσ'mem)
    have e1 : ENNReal.ofReal h * ∑ l : Fin q, weakWordENorm X (U (σ' * r)) [l] P u ≤ Φ₁ := by
      have := le_seminormPhi_noDrift (w := w) X U P r 1 u hσ'mem
      rwa [sum_wordsOfWeight_one_noDrift hw, pow_one] at this
    have e0 : weakWordENorm X (U (σ' * r)) [] P u ≤ Φ₀ := by
      have := le_seminormPhi_noDrift (w := w) X U P r 0 u hσ'mem
      rwa [wordsOfWeight_zero, Finset.sum_singleton, pow_zero, ENNReal.ofReal_one, one_mul] at this
    calc ENNReal.ofReal (((1 - σ) * r) ^ 1) *
          ∑ I ∈ wordsOfWeight w 1, weakWordENorm X (U (σ * r)) I P u
        = ENNReal.ofReal (2 * h) * ∑ l : Fin q, weakWordENorm X (U (σ * r)) [l] P u := by
          rw [sum_wordsOfWeight_one_noDrift hw, pow_one, hlhs]
      _ ≤ _ := hscale
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul' le_rfl e2) (mul_le_mul' le_rfl e1))
          (mul_le_mul' le_rfl e0)
  have hΦ₁le : Φ₁ ≤ ENNReal.ofReal (2 * τ) * Φ₂ + ENNReal.ofReal (4 * B * τ) * Φ₁ +
      ENNReal.ofReal (2 * τ * ((q : ℝ) + 1) * B + 2 * Cp / τ) * Φ₀ := by
    rw [hΦ₁]
    unfold seminormPhi
    exact iSup₂_le hσ
  have hc : 4 * B * τ ≤ 1 / 2 := four_mul_tau_le hδ hδ2 hB
  have habs := ennreal_absorb (A := ENNReal.ofReal (2 * τ) * Φ₂ +
      ENNReal.ofReal (2 * τ * ((q : ℝ) + 1) * B + 2 * Cp / τ) * Φ₀) hfin hc
    (by calc Φ₁ ≤ _ := hΦ₁le
          _ = _ := by ring)
  refine habs.trans ?_
  have hK1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) q]
  have hreal := absorb_const_le (Cp := Cp) (K := (q : ℝ) + 1) hδ hδ2 hB hCp hK1
  have e2 : (2 : ℝ≥0∞) * (ENNReal.ofReal (2 * τ) * Φ₂ +
      ENNReal.ofReal (2 * τ * ((q : ℝ) + 1) * B + 2 * Cp / τ) * Φ₀) =
      ENNReal.ofReal (4 * τ) * Φ₂ + ENNReal.ofReal (2 * (2 * τ * ((q : ℝ) + 1) * B +
        2 * Cp / τ)) * Φ₀ := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    have h4 : 2 * (2 * τ) = 4 * τ := by ring
    rw [mul_add, ← mul_assoc, ← mul_assoc, h2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), h4]
  rw [e2]
  refine add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hτδ) le_rfl)
    (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have h6 : 2 * (2 * τ * ((q : ℝ) + 1) * B + 2 * Cp / τ) =
      4 * τ * ((q : ℝ) + 1) * B + 4 * Cp / τ := by ring
  rw [h6]
  exact hreal

end MainNoDrift

end RothschildStein.P2

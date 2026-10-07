-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationStep

/-!
# Sobolev interpolation, seminorm absorption: `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀`

Abstract absorption argument of the Sobolev interpolation inequality (BB p. 583, Thm 11.39; its prototype is BB p. 371,
Thm 8.42), for a family `Uρ` of nested open sets (the `ρ`-balls) and cutoffs between `U_{σ r}` and
`U_{σ' r}`, `σ' = (1 + σ)/2`, with the weighted derivative bounds `|X̃_I φ| ≤ B (t - s)^{-|I|}`.

For `σ ∈ [1/2, 1)`, `h = (1 - σ') r = (t - s)`, apply `seminorm_step` with `ε = τ h`:
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

section Algebra

/-- Absorption in `ℝ≥0∞`: `x ≤ A + c x`, `c ≤ 1/2`, `x < ∞` give `x ≤ 2 A`. -/
theorem ennreal_absorb {x A : ℝ≥0∞} {c : ℝ} (hx : x ≠ ⊤) (hc : c ≤ 1 / 2)
    (h : x ≤ A + ENNReal.ofReal c * x) : x ≤ 2 * A := by
  have hc' : ENNReal.ofReal c ≤ 2⁻¹ := by
    calc ENNReal.ofReal c ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hc
      _ = 2⁻¹ := by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  have h2 : x ≤ A + 2⁻¹ * x := h.trans (add_le_add le_rfl (mul_le_mul' hc' le_rfl))
  have hsplit : x = 2⁻¹ * x + 2⁻¹ * x := by
    rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hfin : 2⁻¹ * x ≠ ⊤ := ENNReal.mul_ne_top (by simp) hx
  have h3 : 2⁻¹ * x + 2⁻¹ * x ≤ A + 2⁻¹ * x := by
    calc 2⁻¹ * x + 2⁻¹ * x = x := hsplit.symm
      _ ≤ _ := h2
  have h4 : 2⁻¹ * x ≤ A := (ENNReal.add_le_add_iff_right hfin).1 h3
  calc x = 2 * (2⁻¹ * x) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * A := mul_le_mul' le_rfl h4

/-- `ofReal a * ofReal b = ofReal (a b)` for `a ≥ 0`. -/
theorem ofReal_mul_ofReal {a : ℝ} (b : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) :=
  (ENNReal.ofReal_mul ha).symm

/-- Multiplication of the cutoff-step inequality by `2h`. -/
theorem step_scale {q : ℕ} {h τ B Cp : ℝ} (hh : 0 < h) (hτ : 0 < τ) (hB : 0 ≤ B) (hCp : 0 ≤ Cp)
    {S T2 T1 N0 : ℝ≥0∞}
    (hS : S ≤ ENNReal.ofReal (τ * h) * (T2 + ENNReal.ofReal (2 * (B / h)) * T1 +
        ((q : ℝ≥0∞) + 1) * ENNReal.ofReal (B / h ^ 2) * N0) +
      ENNReal.ofReal (Cp / (τ * h)) * N0) :
    ENNReal.ofReal (2 * h) * S ≤ ENNReal.ofReal (2 * τ) * (ENNReal.ofReal (h ^ 2) * T2) +
      ENNReal.ofReal (4 * B * τ) * (ENNReal.ofReal h * T1) +
      ENNReal.ofReal (2 * τ * ((q : ℝ) + 1) * B + 2 * Cp / τ) * N0 := by
  have hh0 : h ≠ 0 := hh.ne'
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hq1 : ((q : ℝ≥0∞) + 1) = ENNReal.ofReal ((q : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg q) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  have eq1 : ENNReal.ofReal (2 * h) * ENNReal.ofReal (τ * h) =
      ENNReal.ofReal (2 * τ) * ENNReal.ofReal (h ^ 2) := by
    rw [ofReal_mul_ofReal _ (by positivity), ofReal_mul_ofReal _ (by positivity)]
    congr 1
    ring
  have eq2 : ENNReal.ofReal (2 * h) * ENNReal.ofReal (τ * h) * ENNReal.ofReal (2 * (B / h)) =
      ENNReal.ofReal (4 * B * τ) * ENNReal.ofReal h := by
    rw [ofReal_mul_ofReal _ (by positivity), ofReal_mul_ofReal _ (by positivity),
      ofReal_mul_ofReal _ (by positivity)]
    congr 1
    field_simp
    ring
  have eq3 : ENNReal.ofReal (2 * h) * ENNReal.ofReal (τ * h) * (((q : ℝ≥0∞) + 1) *
        ENNReal.ofReal (B / h ^ 2)) + ENNReal.ofReal (2 * h) * ENNReal.ofReal (Cp / (τ * h)) =
      ENNReal.ofReal (2 * τ * ((q : ℝ) + 1) * B + 2 * Cp / τ) := by
    rw [hq1, ofReal_mul_ofReal _ (by positivity), ofReal_mul_ofReal _ (by positivity),
      ofReal_mul_ofReal _ (by positivity), ofReal_mul_ofReal _ (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
  calc ENNReal.ofReal (2 * h) * S
      ≤ ENNReal.ofReal (2 * h) * (ENNReal.ofReal (τ * h) * (T2 + ENNReal.ofReal (2 * (B / h)) * T1 +
        ((q : ℝ≥0∞) + 1) * ENNReal.ofReal (B / h ^ 2) * N0) +
        ENNReal.ofReal (Cp / (τ * h)) * N0) := mul_le_mul' le_rfl hS
    _ = (ENNReal.ofReal (2 * h) * ENNReal.ofReal (τ * h)) * T2 +
        (ENNReal.ofReal (2 * h) * ENNReal.ofReal (τ * h) * ENNReal.ofReal (2 * (B / h))) * T1 +
        (ENNReal.ofReal (2 * h) * ENNReal.ofReal (τ * h) * (((q : ℝ≥0∞) + 1) *
          ENNReal.ofReal (B / h ^ 2)) + ENNReal.ofReal (2 * h) * ENNReal.ofReal (Cp / (τ * h))) *
          N0 := by ring
    _ = _ := by rw [eq2, eq3, eq1]; ring

/-- Real arithmetic of the absorption: `4 B τ ≤ 1/2` for `τ = δ/(4(1+B))`, `δ ≤ 1/2`. -/
theorem four_mul_tau_le {δ B : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hB : 0 ≤ B) :
    4 * B * (δ / (4 * (1 + B))) ≤ 1 / 2 := by
  have hB1 : 0 < 1 + B := by linarith
  have e : 4 * B * (δ / (4 * (1 + B))) = δ * (B / (1 + B)) := by field_simp
  rw [e]
  have hb : B / (1 + B) ≤ 1 := by rw [div_le_one hB1]; linarith
  have hb0 : 0 ≤ B / (1 + B) := by positivity
  nlinarith

/-- `4 τ ≤ δ` for `τ = δ/(4(1+B))`. -/
theorem four_tau_le {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) : 4 * (δ / (4 * (1 + B))) ≤ δ := by
  have hB1 : 0 < 1 + B := by linarith
  have e : 4 * (δ / (4 * (1 + B))) = δ / (1 + B) := by field_simp
  rw [e]
  exact div_le_self hδ.le (by linarith)

/-- Real arithmetic of the absorption: the constant in front of `Φ₀`. -/
theorem absorb_const_le {δ B Cp K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hB : 0 ≤ B) (_hCp : 0 ≤ Cp)
    (hK : 1 ≤ K) :
    4 * (δ / (4 * (1 + B))) * K * B + 4 * Cp / (δ / (4 * (1 + B))) ≤
      (K + 16 * Cp * (1 + B)) / δ := by
  have hB1 : 0 < 1 + B := by linarith
  have e2 : 4 * Cp / (δ / (4 * (1 + B))) = 16 * Cp * (1 + B) / δ := by
    field_simp
    ring
  have h1 : 4 * (δ / (4 * (1 + B))) * K * B ≤ K / δ := by
    have e1 : 4 * (δ / (4 * (1 + B))) * K * B = K * δ * (B / (1 + B)) := by field_simp
    have hb : B / (1 + B) ≤ 1 := by rw [div_le_one hB1]; linarith
    have h5 : K * δ ≤ K / δ := by
      rw [le_div_iff₀ hδ]
      have hδδ : δ * δ ≤ 1 := by nlinarith
      calc K * δ * δ = K * (δ * δ) := by ring
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left hδδ (by linarith)
        _ = K := mul_one K
    rw [e1]
    calc K * δ * (B / (1 + B)) ≤ K * δ * 1 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ K / δ := by rw [mul_one]; exact h5
  rw [e2, add_div]
  linarith

end Algebra

section Main

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}

/-- Every term of the supremum defining `seminormPhi` is at most `seminormPhi`. -/
theorem le_seminormPhi (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (U : ℝ → Opens (Fin n → ℝ)) (p : ℝ≥0∞) (r : ℝ) (j : ℕ) (u : (Fin n → ℝ) → ℝ) {σ : ℝ}
    (hσ : σ ∈ Set.Ico (1 / 2 : ℝ) 1) :
    ENNReal.ofReal (((1 - σ) * r) ^ j) *
        ∑ I ∈ wordsOfWeight w j, weakWordENorm X (U (σ * r)) I p u ≤
      seminormPhi w X U p r j u :=
  le_iSup₂ (f := fun σ (_ : σ ∈ Set.Ico (1 / 2 : ℝ) 1) => ENNReal.ofReal (((1 - σ) * r) ^ j) *
    ∑ I ∈ wordsOfWeight w j, weakWordENorm X (U (σ * r)) I p u) σ hσ

/-- The cutoffs from the radial cutoff construction between `U_{σ r}` and `U_{σ' r}`, `σ' = (1 + σ)/2`, `σ ∈ [1/2, 1)`:
`φ ∈ C_c^∞(U_r)` with `0 ≤ φ ≤ 1`, `φ = 1` on `U_{σ r}`, `tsupport φ ⊆ U_{σ' r}` and the weighted
derivative bounds `|X̃_I φ| ≤ B (t - s)^{-|I|}`, `t - s = (1 - σ') r`, for the words `[l+1]`
(weight one), `[l+1, l+1]` and `[0]` (weight two). -/
def CutoffFamily (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (U : ℝ → Opens (Fin n → ℝ))
    (r B : ℝ) : Prop :=
  ∀ σ ∈ Set.Ico (1 / 2 : ℝ) 1, ∃ φ : TestFunction (U r) ℝ (⊤ : ℕ∞),
    (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x ∈ (U (σ * r) : Set (Fin n → ℝ)), φ x = 1) ∧
    tsupport (φ : (Fin n → ℝ) → ℝ) ⊆ (U (((1 + σ) / 2) * r) : Set (Fin n → ℝ)) ∧
    (∀ (l : Fin q) (x : Fin n → ℝ), |fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ) x| ≤
      B / ((1 - (1 + σ) / 2) * r)) ∧
    (∀ (l : Fin q) (x : Fin n → ℝ),
      |fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (φ : (Fin n → ℝ) → ℝ)) x| ≤
        B / ((1 - (1 + σ) / 2) * r) ^ 2) ∧
    (∀ x : Fin n → ℝ, |fieldDerivative (X 0) (φ : (Fin n → ℝ) → ℝ) x| ≤
      B / ((1 - (1 + σ) / 2) * r) ^ 2)

/-- **The absorption inequality** `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀`
(BB p. 583, Thm 11.39), for a nested family `U` of open sets with cutoffs (`CutoffFamily`), on which
the compact interpolation inequality `CompactInterpolationOn` holds with constants `εs, Cp`:
for `0 < δ ≤ 1/2`, `δ < εs`, `0 < r ≤ 1` and `u ∈ W^{2,p}_{X̃}(U_r)`,
`Φ₁ ≤ δ Φ₂ + ((q + 1 + 16 Cp (1 + B))/δ) Φ₀`. -/
theorem seminormPhi_absorption
    (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p εs Cp : ℝ} (hp : 1 < p) (hCp : 0 ≤ Cp)
    (hCI : CompactInterpolationOn X V a p εs Cp) {U : ℝ → Opens (Fin n → ℝ)}
    (hmono : ∀ s t : ℝ, s ≤ t → U s ≤ U t) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hrV : U r ≤ V)
    (hra : ∀ x ∈ (U r : Set (Fin n → ℝ)), a x = 1) {B : ℝ} (hB : 0 ≤ B)
    (hcut : CutoffFamily X U r B) {u : (Fin n → ℝ) → ℝ}
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
  have hmem1 : ∀ l : Fin q, [l.succ] ∈ wordFamily w 2 := fun l => by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw l]
  choose g1 hg1 using fun l : Fin q => hu.2 [l.succ] (hmem1 l)
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
      rw [sum_wordsOfWeight_one hw hw0, pow_one]
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
    obtain ⟨φ, hφ0, hφ1, hφs, hφt, hb1, hb2, hbd⟩ := hcut σ hσ
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
    have hstep := seminorm_step hw hw0 hXV hp hCI (Ω' := U r) (Us := U (σ * r))
      (Ut := U (σ' * r)) hrV hra hUs hUt hu φ hφ0 hφ1 hφs hφt (b1 := B / h) (b2 := B / h ^ 2)
      (by positivity) (by positivity) hb1 hb2 hbd (ε := τ * h) (by positivity)
      (by nlinarith)
    have hscale := step_scale (q := q) hh0 hτ0 hB hCp hstep
    have hlhs : (1 - σ) * r = 2 * h := by rw [hh, hσ']; ring
    -- the three terms on the right
    have e2 : ENNReal.ofReal (h ^ 2) * (∑ l : Fin q,
        weakWordENorm X (U (σ' * r)) [l.succ, l.succ] P u + weakWordENorm X (U (σ' * r)) [0] P u) ≤ Φ₂ :=
      (mul_le_mul' le_rfl (sum_wordsOfWeight_two_ge hw hw0 _)).trans
        (le_seminormPhi X U P r 2 u hσ'mem)
    have e1 : ENNReal.ofReal h * ∑ l : Fin q, weakWordENorm X (U (σ' * r)) [l.succ] P u ≤ Φ₁ := by
      have := le_seminormPhi (w := w) X U P r 1 u hσ'mem
      rwa [sum_wordsOfWeight_one hw hw0, pow_one] at this
    have e0 : weakWordENorm X (U (σ' * r)) [] P u ≤ Φ₀ := by
      have := le_seminormPhi (w := w) X U P r 0 u hσ'mem
      rwa [wordsOfWeight_zero, Finset.sum_singleton, pow_zero, ENNReal.ofReal_one, one_mul] at this
    calc ENNReal.ofReal (((1 - σ) * r) ^ 1) *
          ∑ I ∈ wordsOfWeight w 1, weakWordENorm X (U (σ * r)) I P u
        = ENNReal.ofReal (2 * h) * ∑ l : Fin q, weakWordENorm X (U (σ * r)) [l.succ] P u := by
          rw [sum_wordsOfWeight_one hw hw0, pow_one, hlhs]
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

end Main

end RothschildStein.P2

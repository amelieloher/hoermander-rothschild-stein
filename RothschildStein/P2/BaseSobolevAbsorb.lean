-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseSobolevStep
public import RothschildStein.P2.SobolevInterpolationAbsorb

/-!
# `Φ₂ + Φ₁ ≤ C (r² ‖L̃u‖ + ‖u‖)`

Part of the base Sobolev estimate (BB pp. 586-587, (11.69)-(11.72)). For a nested family `U` of open sets (the `ρ`-balls) with
cutoffs `φ` between `U_{σ r}` and `U_{σ' r}`, `σ' = (1 + σ)/2` (`CutoffFamily`, constant `B`), the cutoff
step `second_step` for the words of weight two reads, with `a = (1 - σ) r = 2h`, `h = (1 - σ') r`,

`a² ‖X̃_I u‖_{Us} ≤ C (r² ‖L̃u‖ + a ‖Du‖_{Ut} + ‖u‖_{Ut})`

(`second_scale`). Summing over the words of weight two and taking the supremum over `σ ∈ [1/2, 1)`,

`Φ₂ ≤ C₁ r² ‖L̃u‖ + C₂ Φ₁ + C₃ Φ₀`.

With the interpolation `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀` of the Sobolev interpolation inequality (`habs`), `δ` with `C₂ δ ≤ 1/2`, and the
finiteness `Φ₂ < ∞` of `u ∈ W^{2,p}`, this gives `Φ₂ + Φ₁ ≤ C (r² ‖L̃u‖_{L^p(U_r)} + Φ₀)`
(`seminormPhi_second_absorption`, `second_absorb_algebra`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein RothschildStein.P1

section Algebra

/-- Multiplication of the per-word bound of `second_step` by `a² = 4 h²`, `a = (1 - σ) r = 2 h`
(BB (11.69)-(11.70)): the three terms become `r² ‖f‖`, `h ‖Du‖` and `‖u‖` with constants independent of
`h ≤ r ≤ 1`. Here `N` is the number of words of weight two. -/
theorem second_scale {q : ℕ} {h r Λ B : ℝ} (N : ℕ) (hh : 0 < h) (hhr : h ≤ r) (hr1 : r ≤ 1)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B) {S F T1 N0 : ℝ≥0∞}
    (hS : S ≤ (N : ℝ≥0∞) * (ENNReal.ofReal Λ * (F + ENNReal.ofReal (2 * (B / h)) * T1 +
        (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) * N0))) :
    ENNReal.ofReal (4 * h ^ 2) * S ≤
      ENNReal.ofReal (4 * ((N : ℝ) * Λ) * r ^ 2) * F +
        ENNReal.ofReal (8 * ((N : ℝ) * Λ) * B) * (ENNReal.ofReal h * T1) +
        ENNReal.ofReal (4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + 1)) * N0 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hh0 : h ≠ 0 := hh.ne'
  have c1 : ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ =
      ENNReal.ofReal (4 * h ^ 2 * N * Λ) := by
    rw [← ENNReal.ofReal_natCast N, ofReal_mul_ofReal _ (by positivity),
      ofReal_mul_ofReal _ (by positivity)]
  have c2 : ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ *
      ENNReal.ofReal (2 * (B / h)) = ENNReal.ofReal (8 * ((N : ℝ) * Λ) * B) * ENNReal.ofReal h := by
    rw [c1, ofReal_mul_ofReal _ (by positivity), ofReal_mul_ofReal _ (by positivity)]
    congr 1
    field_simp
    ring
  have c3 : ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ *
        ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) +
      ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ =
      ENNReal.ofReal (4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + h ^ 2)) := by
    rw [c1, ofReal_mul_ofReal _ (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    congr 1
    field_simp
  have hh2 : h ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hh.le hhr 2
  have hh2' : h ^ 2 ≤ 1 := by nlinarith
  have hNΛ : 0 ≤ (N : ℝ) * Λ := mul_nonneg hN hΛ
  calc ENNReal.ofReal (4 * h ^ 2) * S
      ≤ ENNReal.ofReal (4 * h ^ 2) * ((N : ℝ≥0∞) * (ENNReal.ofReal Λ * (F +
          ENNReal.ofReal (2 * (B / h)) * T1 +
          (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) * N0))) := mul_le_mul' le_rfl hS
    _ = (ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ) * F +
        (ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ *
          ENNReal.ofReal (2 * (B / h))) * T1 +
        (ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ *
          ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) +
          ENNReal.ofReal (4 * h ^ 2) * (N : ℝ≥0∞) * ENNReal.ofReal Λ) * N0 := by ring
    _ = ENNReal.ofReal (4 * h ^ 2 * N * Λ) * F +
        ENNReal.ofReal (8 * ((N : ℝ) * Λ) * B) * (ENNReal.ofReal h * T1) +
        ENNReal.ofReal (4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + h ^ 2)) * N0 := by
      rw [c2, c3, c1]
      ring
    _ ≤ _ := by
      refine add_le_add (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl)
        (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      · have : 4 * h ^ 2 * N * Λ = 4 * ((N : ℝ) * Λ) * h ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hh2 (by positivity)
      · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **The absorption algebra** (BB (11.71)-(11.72)): from
`Φ₂ ≤ α F' + β Φ₁ + γ Φ₀` with `Φ₂ < ∞` and the interpolation `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀`
(`0 < δ ≤ δ₀`), choose `δ` with `β δ ≤ 1/2`; then `Φ₂ + Φ₁ ≤ K (F' + Φ₀)` with `K` depending only on
`α, β, γ, δ₀, C`. -/
theorem second_absorb_algebra {α β γ δ₀ Cabs : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hδ₀ : 0 < δ₀) (hCabs : 0 ≤ Cabs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F' Φ₀ Φ₁ Φ₂ : ℝ≥0∞, Φ₂ ≠ ⊤ →
      Φ₂ ≤ ENNReal.ofReal α * F' + ENNReal.ofReal β * Φ₁ + ENNReal.ofReal γ * Φ₀ →
      (∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        Φ₁ ≤ ENNReal.ofReal δ * Φ₂ + ENNReal.ofReal (Cabs / δ) * Φ₀) →
      Φ₂ + Φ₁ ≤ ENNReal.ofReal K * (F' + Φ₀) := by
  have hβ1 : 0 < 2 * β + 1 := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ₀ (1 / (2 * β + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min hδ₀ (by positivity)
  have hδδ₀ : δ ≤ δ₀ := by
    rw [hδdef]
    exact min_le_left _ _
  have hδβ : δ ≤ 1 / (2 * β + 1) := by
    rw [hδdef]
    exact min_le_right _ _
  have hβδ : β * δ ≤ 1 / 2 := by
    have h1 : β * δ ≤ β * (1 / (2 * β + 1)) := mul_le_mul_of_nonneg_left hδβ hβ
    have h2 : β * (1 / (2 * β + 1)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ hβ1 (by norm_num)]
      nlinarith
    linarith
  have hCδ : 0 ≤ Cabs / δ := div_nonneg hCabs hδ0.le
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = α + β * (Cabs / δ) + γ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have := mul_nonneg hβ hCδ
    linarith
  refine ⟨(1 + δ) * 2 * M + Cabs / δ, by positivity, fun F' Φ₀ Φ₁ Φ₂ hfin h1 h2 => ?_⟩
  have h2' := h2 δ hδ0 hδδ₀
  have hA : Φ₂ ≤ (ENNReal.ofReal α * F' +
      (ENNReal.ofReal (β * (Cabs / δ)) + ENNReal.ofReal γ) * Φ₀) +
        ENNReal.ofReal (β * δ) * Φ₂ := by
    calc Φ₂ ≤ ENNReal.ofReal α * F' + ENNReal.ofReal β * Φ₁ + ENNReal.ofReal γ * Φ₀ := h1
      _ ≤ ENNReal.ofReal α * F' + ENNReal.ofReal β * (ENNReal.ofReal δ * Φ₂ +
          ENNReal.ofReal (Cabs / δ) * Φ₀) + ENNReal.ofReal γ * Φ₀ :=
        add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl h2')) le_rfl
      _ = _ := by
        rw [ENNReal.ofReal_mul hβ, ENNReal.ofReal_mul hβ]
        ring
  have h3 := ennreal_absorb hfin hβδ hA
  have h4 : Φ₂ + Φ₁ ≤ ENNReal.ofReal (1 + δ) * Φ₂ + ENNReal.ofReal (Cabs / δ) * Φ₀ := by
    calc Φ₂ + Φ₁ ≤ Φ₂ + (ENNReal.ofReal δ * Φ₂ + ENNReal.ofReal (Cabs / δ) * Φ₀) :=
          add_le_add le_rfl h2'
      _ = _ := by
        rw [ENNReal.ofReal_add zero_le_one hδ0.le, ENNReal.ofReal_one]
        ring
  have h5 : ENNReal.ofReal (1 + δ) * Φ₂ ≤ ENNReal.ofReal ((1 + δ) * 2 * M) * (F' + Φ₀) := by
    have hcoef : ENNReal.ofReal (β * (Cabs / δ)) + ENNReal.ofReal γ ≤ ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_add (mul_nonneg hβ hCδ) hγ]
      exact ENNReal.ofReal_le_ofReal (by rw [hMdef]; linarith)
    have h2e : ENNReal.ofReal 2 = 2 := by simp
    have hαM : ENNReal.ofReal α ≤ ENNReal.ofReal M :=
      ENNReal.ofReal_le_ofReal (by
        rw [hMdef]
        have := mul_nonneg hβ hCδ
        linarith)
    calc ENNReal.ofReal (1 + δ) * Φ₂
        ≤ ENNReal.ofReal (1 + δ) * (2 * (ENNReal.ofReal α * F' +
          (ENNReal.ofReal (β * (Cabs / δ)) + ENNReal.ofReal γ) * Φ₀)) := mul_le_mul' le_rfl h3
      _ = ENNReal.ofReal ((1 + δ) * 2) * (ENNReal.ofReal α * F' +
          (ENNReal.ofReal (β * (Cabs / δ)) + ENNReal.ofReal γ) * Φ₀) := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + δ by positivity), h2e]
        ring
      _ ≤ ENNReal.ofReal ((1 + δ) * 2) * (ENNReal.ofReal M * F' + ENNReal.ofReal M * Φ₀) :=
        mul_le_mul' le_rfl (add_le_add (mul_le_mul' hαM le_rfl) (mul_le_mul' hcoef le_rfl))
      _ = _ := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (1 + δ) * 2 by positivity)]
        ring
  calc Φ₂ + Φ₁ ≤ ENNReal.ofReal (1 + δ) * Φ₂ + ENNReal.ofReal (Cabs / δ) * Φ₀ := h4
    _ ≤ ENNReal.ofReal ((1 + δ) * 2 * M) * (F' + Φ₀) +
        ENNReal.ofReal (Cabs / δ) * (F' + Φ₀) :=
      add_le_add h5 (mul_le_mul' le_rfl le_add_self)
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) hCδ]
      ring

end Algebra

section Main

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}

/-- Restricting a weak word of a Sobolev function to a smaller open set does not increase its norm. -/
theorem weakWordENorm_mono_of_memSobolevX {Ω' U : Opens (Fin n → ℝ)} {p : ℝ≥0∞}
    {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X Ω' 2 p u) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω')
    {I : List (Fin (q + 1))} (hI : I ∈ wordFamily w 2) :
    weakWordENorm X U I p u ≤ weakWordENorm X Ω' I p u := by
  obtain ⟨g, hg, -⟩ := hu.2 I hI
  exact RothschildStein.H3.weakWordENorm_mono_domain X Ω' U hU I p u g hg

/-- `Φ₂(u) < ∞` for `u ∈ W^{2,p}_{X̃}(U_r)`. -/
theorem seminormPhi_two_ne_top {U : ℝ → Opens (Fin n → ℝ)}
    (hmono : ∀ s t : ℝ, s ≤ t → U s ≤ U t) {p : ℝ≥0∞} {r : ℝ} (hr0 : 0 < r)
    {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X (U r) 2 p u) :
    seminormPhi w X U p r 2 u ≠ ⊤ := by
  have hmem : ∀ I ∈ wordsOfWeight w 2, I ∈ wordFamily w 2 := fun I hI => by
    rw [S.mem_wordFamily_iff]
    exact ((mem_wordsOfWeight w).1 hI).le
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (r ^ 2) *
    ∑ I ∈ wordsOfWeight w 2, weakWordENorm X (U r) I p u) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun I hI =>
      (RothschildStein.H3.weakWordENorm_lt_top_of_memSobolev w X (U r) 2 p u hu I (hmem I hI)).ne)
  · unfold seminormPhi
    refine iSup₂_le fun σ hσ => ?_
    have hσr : σ * r ≤ r := mul_le_of_le_one_left hr0.le hσ.2.le
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (Finset.sum_le_sum fun I hI => ?_)
    · have h1 : 0 ≤ (1 - σ) * r := mul_nonneg (by linarith [hσ.2]) hr0.le
      have h2 : (1 - σ) * r ≤ r := by nlinarith [hσ.1]
      exact pow_le_pow_left₀ h1 h2 2
    · exact weakWordENorm_mono_of_memSobolevX hu (hmono _ _ hσr) (hmem I hI)

/-- **The absorption `Φ₂ + Φ₁ ≤ C (r² ‖L̃u‖ + Φ₀)`** (BB pp. 586-587,
(11.69)-(11.72)). Let `U` be a nested family of open sets with cutoffs (`CutoffFamily`, constant `B`)
on which the compact second-derivative estimate `CompactSecondOn` holds (constants `p, Λ`). There is a
constant `K` (depending only on `Λ, B, q`, the number of words of weight two, `δ₀` and `Cabs`) such
that for `0 < r ≤ 1` with `U_r ≤ V`, `a = 1` on `U_r`, `u ∈ W^{2,p}_{X̃}(U_r)` with `L̃u = f` weakly, and
the interpolation `Φ₁ ≤ δ Φ₂ + Cabs δ^{-1} Φ₀` of the Sobolev interpolation inequality for `0 < δ ≤ δ₀`,
`Φ₂ + Φ₁ ≤ K (r² ‖f‖_{L^p(U_r)} + Φ₀)`. -/
theorem seminormPhi_second_absorption
    (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p Λ : ℝ} (hp : 1 < p) (hΛ : 0 ≤ Λ)
    (hCS : CompactSecondOn w X V a p Λ) {U : ℝ → Opens (Fin n → ℝ)}
    (hmono : ∀ s t : ℝ, s ≤ t → U s ≤ U t) {B : ℝ} (hB : 0 ≤ B) {δ₀ Cabs : ℝ} (hδ₀ : 0 < δ₀)
    (hCabs : 0 ≤ Cabs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → U r ≤ V →
      (∀ x ∈ (U r : Set (Fin n → ℝ)), a x = 1) → CutoffFamily X U r B →
      ∀ u f : (Fin n → ℝ) → ℝ, memSobolevX w X (U r) 2 (ENNReal.ofReal p) u →
        HasWeakOperatorValue X (U r) (driftOpWords q) u f →
        (∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          seminormPhi w X U (ENNReal.ofReal p) r 1 u ≤
            ENNReal.ofReal δ * seminormPhi w X U (ENNReal.ofReal p) r 2 u +
              ENNReal.ofReal (Cabs / δ) * seminormPhi w X U (ENNReal.ofReal p) r 0 u) →
        seminormPhi w X U (ENNReal.ofReal p) r 2 u + seminormPhi w X U (ENNReal.ofReal p) r 1 u ≤
          ENNReal.ofReal K * (ENNReal.ofReal (r ^ 2) *
            eLpNorm f (ENNReal.ofReal p) (volume.restrict (U r : Set (Fin n → ℝ))) +
            seminormPhi w X U (ENNReal.ofReal p) r 0 u) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (wordsOfWeight w 2).card := ⟨_, rfl⟩
  have hNΛ : 0 ≤ (N : ℝ) * Λ := mul_nonneg (Nat.cast_nonneg N) hΛ
  obtain ⟨K, hK0, hK⟩ := second_absorb_algebra (α := 4 * ((N : ℝ) * Λ))
    (β := 8 * ((N : ℝ) * Λ) * B) (γ := 4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + 1))
    (δ₀ := δ₀) (Cabs := Cabs) (by positivity) (by positivity) (by positivity) hδ₀ hCabs
  refine ⟨K, hK0, fun r hr0 hr1 hrV hra hcut u f hu hf habs => ?_⟩
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨g0, g2, hg0, hg2, hfae⟩ := exists_weakWords_of_hasWeakOperatorValue_drift hf
  have hfin := seminormPhi_two_ne_top (w := w) (X := X) hmono hr0 hu
  refine hK _ _ _ _ hfin ?_ habs
  -- the inequality for each `σ`
  have hσ : ∀ σ ∈ Set.Ico (1 / 2 : ℝ) 1,
      ENNReal.ofReal (((1 - σ) * r) ^ 2) *
          ∑ I ∈ wordsOfWeight w 2, weakWordENorm X (U (σ * r)) I P u ≤
        ENNReal.ofReal (4 * ((N : ℝ) * Λ)) *
            (ENNReal.ofReal (r ^ 2) * eLpNorm f P (volume.restrict (U r : Set (Fin n → ℝ)))) +
          ENNReal.ofReal (8 * ((N : ℝ) * Λ) * B) * seminormPhi w X U P r 1 u +
          ENNReal.ofReal (4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + 1)) *
            seminormPhi w X U P r 0 u := by
    intro σ hσ
    obtain ⟨φ, hφ0, hφ1, hφs, hφt, hb1, hb2, hbd⟩ := hcut σ hσ
    set σ' : ℝ := (1 + σ) / 2 with hσ'
    have hσ'mem : σ' ∈ Set.Ico (1 / 2 : ℝ) 1 := ⟨by rw [hσ']; linarith [hσ.1],
      by rw [hσ']; linarith [hσ.2]⟩
    set h : ℝ := (1 - σ') * r with hh
    have hh0 : 0 < h := mul_pos (by linarith [hσ'mem.2]) hr0
    have hhr : h ≤ r := by nlinarith [hσ'mem.1]
    have hUs : U (σ * r) ≤ U (σ' * r) := hmono _ _ (mul_le_mul_of_nonneg_right
      (by rw [hσ']; linarith [hσ.2]) hr0.le)
    have hUt : U (σ' * r) ≤ U r := hmono _ _ (mul_le_of_le_one_left hr0.le hσ'mem.2.le)
    have hstep : ∀ I ∈ wordsOfWeight w 2, weakWordENorm X (U (σ * r)) I P u ≤
        ENNReal.ofReal Λ * (eLpNorm f P (volume.restrict (U (σ' * r) : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * (B / h)) * ∑ l : Fin q,
            weakWordENorm X (U (σ' * r)) [l.succ] P u +
          (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) *
            weakWordENorm X (U (σ' * r)) [] P u) := fun I hI =>
      second_step hw hw0 hXV hp hCS (Ω' := U r) (Us := U (σ * r)) (Ut := U (σ' * r)) hrV hra hUs
        hUt hu hg0 hg2 hfae φ hφ0 hφ1 hφs hφt (b1 := B / h) (b2 := B / h ^ 2)
        (by positivity) (by positivity) hb1 hb2 hbd hI
    have hsum : ∑ I ∈ wordsOfWeight w 2, weakWordENorm X (U (σ * r)) I P u ≤
        (N : ℝ≥0∞) * (ENNReal.ofReal Λ * (eLpNorm f P
          (volume.restrict (U (σ' * r) : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * (B / h)) * ∑ l : Fin q,
            weakWordENorm X (U (σ' * r)) [l.succ] P u +
          (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) *
            weakWordENorm X (U (σ' * r)) [] P u)) := by
      calc _ ≤ ∑ _I ∈ wordsOfWeight w 2, ENNReal.ofReal Λ * (eLpNorm f P
          (volume.restrict (U (σ' * r) : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * (B / h)) * ∑ l : Fin q,
            weakWordENorm X (U (σ' * r)) [l.succ] P u +
          (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) *
            weakWordENorm X (U (σ' * r)) [] P u) := Finset.sum_le_sum hstep
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ← hN]
    have hscale := second_scale (q := q) N hh0 hhr hr1 hΛ hB hsum
    have hlhs : ((1 - σ) * r) ^ 2 = 4 * h ^ 2 := by
      rw [hh, hσ']
      ring
    have eF : eLpNorm f P (volume.restrict (U (σ' * r) : Set (Fin n → ℝ))) ≤
        eLpNorm f P (volume.restrict (U r : Set (Fin n → ℝ))) :=
      eLpNorm_mono_measure f (Measure.restrict_mono hUt le_rfl)
    have e1 : ENNReal.ofReal h * ∑ l : Fin q, weakWordENorm X (U (σ' * r)) [l.succ] P u ≤
        seminormPhi w X U P r 1 u := by
      have := le_seminormPhi (w := w) X U P r 1 u hσ'mem
      rwa [sum_wordsOfWeight_one hw hw0, pow_one] at this
    have e0 : weakWordENorm X (U (σ' * r)) [] P u ≤ seminormPhi w X U P r 0 u := by
      have := le_seminormPhi (w := w) X U P r 0 u hσ'mem
      rwa [wordsOfWeight_zero, Finset.sum_singleton, pow_zero, ENNReal.ofReal_one, one_mul] at this
    rw [hlhs]
    refine hscale.trans ?_
    refine add_le_add (add_le_add ?_ (mul_le_mul' le_rfl e1)) (mul_le_mul' le_rfl e0)
    calc ENNReal.ofReal (4 * ((N : ℝ) * Λ) * r ^ 2) *
          eLpNorm f P (volume.restrict (U (σ' * r) : Set (Fin n → ℝ)))
        ≤ ENNReal.ofReal (4 * ((N : ℝ) * Λ) * r ^ 2) *
          eLpNorm f P (volume.restrict (U r : Set (Fin n → ℝ))) := mul_le_mul' le_rfl eF
      _ = ENNReal.ofReal (4 * ((N : ℝ) * Λ)) *
          (ENNReal.ofReal (r ^ 2) * eLpNorm f P (volume.restrict (U r : Set (Fin n → ℝ)))) := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 * ((N : ℝ) * Λ) by positivity), mul_assoc]
  exact iSup₂_le hσ

end Main

end RothschildStein.P2

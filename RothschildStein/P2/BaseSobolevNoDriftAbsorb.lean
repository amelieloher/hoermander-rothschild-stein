-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseSobolevNoDriftStep
public import RothschildStein.P2.BaseSobolevNoDriftAlgebra
public import RothschildStein.P2.SobolevInterpolationNoDriftAbsorb

/-!
# No drift: `Φ₂ + Φ₁ ≤ C (r² ‖L̃u‖ + ‖u‖)`

Part of the base Sobolev estimate (BB pp. 586-587, (11.69)-(11.72)), without drift. For a nested family `U` of open sets (the
`ρ`-balls) with cutoffs `φ` between `U_{σ r}` and `U_{σ' r}`, `σ' = (1 + σ)/2` (`CutoffFamilyNoDrift`,
constant `B`), the cutoff step `second_step_noDrift` for the words of weight two reads, with
`a = (1 - σ) r = 2h`, `h = (1 - σ') r`,

`a² ‖X̃_I u‖_{Us} ≤ C (r² ‖L̃u‖ + a ‖Du‖_{Ut} + ‖u‖_{Ut})`

(`second_scale_noDrift`). Summing over the words of weight two and taking the supremum over
`σ ∈ [1/2, 1)`,

`Φ₂ ≤ C₁ r² ‖L̃u‖ + C₂ Φ₁ + C₃ Φ₀`.

With the interpolation `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀` of the Sobolev interpolation inequality (`habs`), `δ` with `C₂ δ ≤ 1/2`, and the
finiteness `Φ₂ < ∞` of `u ∈ W^{2,p}`, this gives `Φ₂ + Φ₁ ≤ C (r² ‖L̃u‖_{L^p(U_r)} + Φ₀)`
(`seminormPhi_second_absorption_noDrift`, `second_absorb_algebra_noDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein RothschildStein.P1

variable {n q : ℕ} {w : Fin q → ℕ+} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}

/-- Restricting a weak word of a Sobolev function to a smaller open set does not increase its norm
(no-drift alphabet). -/
theorem weakWordENorm_mono_of_memSobolevX_noDrift {Ω' U : Opens (Fin n → ℝ)} {p : ℝ≥0∞}
    {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X Ω' 2 p u) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω')
    {I : List (Fin q)} (hI : I ∈ wordFamily w 2) :
    weakWordENorm X U I p u ≤ weakWordENorm X Ω' I p u := by
  obtain ⟨g, hg, -⟩ := hu.2 I hI
  exact RothschildStein.H3.weakWordENorm_mono_domain X Ω' U hU I p u g hg

/-- `Φ₂(u) < ∞` for `u ∈ W^{2,p}_{X̃}(U_r)` (no drift). -/
theorem seminormPhi_two_ne_top_noDrift {U : ℝ → Opens (Fin n → ℝ)}
    (hmono : ∀ s t : ℝ, s ≤ t → U s ≤ U t) {p : ℝ≥0∞} {r : ℝ} (hr0 : 0 < r)
    {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X (U r) 2 p u) :
    seminormPhi w X U p r 2 u ≠ ⊤ := by
  have hmem : ∀ I ∈ wordsOfWeight w 2, I ∈ wordFamily w 2 := fun I hI =>
    mem_wordFamily_two_of_mem_wordsOfWeight_two_noDrift hI
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
    · exact weakWordENorm_mono_of_memSobolevX_noDrift hu (hmono _ _ hσr) (hmem I hI)

/-- **The absorption `Φ₂ + Φ₁ ≤ C (r² ‖L̃u‖ + Φ₀)`, no drift** (BB pp. 586-587,
(11.69)-(11.72)). Let `U` be a nested family of open sets with cutoffs (`CutoffFamilyNoDrift`, constant
`B`) on which the compact second-derivative estimate `CompactSecondOnNoDrift` holds (constants `p, Λ`).
There is a constant `K` (depending only on `Λ, B, q`, the number of words of weight two, `δ₀` and `Cabs`)
such that for `0 < r ≤ 1` with `U_r ≤ V`, `a = 1` on `U_r`, `u ∈ W^{2,p}_{X̃}(U_r)` with `L̃u = f` weakly,
and the interpolation `Φ₁ ≤ δ Φ₂ + Cabs δ^{-1} Φ₀` of the Sobolev interpolation inequality for `0 < δ ≤ δ₀`,
`Φ₂ + Φ₁ ≤ K (r² ‖f‖_{L^p(U_r)} + Φ₀)`. -/
theorem seminormPhi_second_absorption_noDrift
    (hw : ∀ j, (w j : ℕ) = 1) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p Λ : ℝ} (hp : 1 < p) (hΛ : 0 ≤ Λ)
    (hCS : CompactSecondOnNoDrift w X V a p Λ) {U : ℝ → Opens (Fin n → ℝ)}
    (hmono : ∀ s t : ℝ, s ≤ t → U s ≤ U t) {B : ℝ} (hB : 0 ≤ B) {δ₀ Cabs : ℝ} (hδ₀ : 0 < δ₀)
    (hCabs : 0 ≤ Cabs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → U r ≤ V →
      (∀ x ∈ (U r : Set (Fin n → ℝ)), a x = 1) → CutoffFamilyNoDrift X U r B →
      ∀ u f : (Fin n → ℝ) → ℝ, memSobolevX w X (U r) 2 (ENNReal.ofReal p) u →
        HasWeakOperatorValue X (U r) (noDriftOpWords q) u f →
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
  obtain ⟨K, hK0, hK⟩ := second_absorb_algebra_noDrift (α := 4 * ((N : ℝ) * Λ))
    (β := 8 * ((N : ℝ) * Λ) * B) (γ := 4 * ((N : ℝ) * Λ) * (((q : ℝ) + 1) * B + 1))
    (δ₀ := δ₀) (Cabs := Cabs) (by positivity) (by positivity) (by positivity) hδ₀ hCabs
  refine ⟨K, hK0, fun r hr0 hr1 hrV hra hcut u f hu hf habs => ?_⟩
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨g2, hg2, hfae⟩ := exists_weakWords_of_hasWeakOperatorValue_noDrift hf
  have hfin := seminormPhi_two_ne_top_noDrift (w := w) (X := X) hmono hr0 hu
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
    obtain ⟨φ, hφ0, hφ1, hφs, hφt, hb1, hb2⟩ := hcut σ hσ
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
            weakWordENorm X (U (σ' * r)) [l] P u +
          (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) *
            weakWordENorm X (U (σ' * r)) [] P u) := fun I hI =>
      second_step_noDrift hw hXV hp hCS (Ω' := U r) (Us := U (σ * r)) (Ut := U (σ' * r)) hrV hra
        hUs hUt hu hg2 hfae φ hφ0 hφ1 hφs hφt (b1 := B / h) (b2 := B / h ^ 2)
        (by positivity) (by positivity) hb1 hb2 hI
    have hsum : ∑ I ∈ wordsOfWeight w 2, weakWordENorm X (U (σ * r)) I P u ≤
        (N : ℝ≥0∞) * (ENNReal.ofReal Λ * (eLpNorm f P
          (volume.restrict (U (σ' * r) : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * (B / h)) * ∑ l : Fin q,
            weakWordENorm X (U (σ' * r)) [l] P u +
          (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) *
            weakWordENorm X (U (σ' * r)) [] P u)) := by
      calc _ ≤ ∑ _I ∈ wordsOfWeight w 2, ENNReal.ofReal Λ * (eLpNorm f P
          (volume.restrict (U (σ' * r) : Set (Fin n → ℝ))) +
          ENNReal.ofReal (2 * (B / h)) * ∑ l : Fin q,
            weakWordENorm X (U (σ' * r)) [l] P u +
          (ENNReal.ofReal (((q : ℝ) + 1) * (B / h ^ 2)) + 1) *
            weakWordENorm X (U (σ' * r)) [] P u) := Finset.sum_le_sum hstep
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ← hN]
    have hscale := second_scale_noDrift (q := q) N hh0 hhr hr1 hΛ hB hsum
    have hlhs : ((1 - σ) * r) ^ 2 = 4 * h ^ 2 := by
      rw [hh, hσ']
      ring
    have eF : eLpNorm f P (volume.restrict (U (σ' * r) : Set (Fin n → ℝ))) ≤
        eLpNorm f P (volume.restrict (U r : Set (Fin n → ℝ))) :=
      eLpNorm_mono_measure f (Measure.restrict_mono hUt le_rfl)
    have e1 : ENNReal.ofReal h * ∑ l : Fin q, weakWordENorm X (U (σ' * r)) [l] P u ≤
        seminormPhi w X U P r 1 u := by
      have := le_seminormPhi_noDrift (w := w) X U P r 1 u hσ'mem
      rwa [sum_wordsOfWeight_one_noDrift hw, pow_one] at this
    have e0 : weakWordENorm X (U (σ' * r)) [] P u ≤ seminormPhi w X U P r 0 u := by
      have := le_seminormPhi_noDrift (w := w) X U P r 0 u hσ'mem
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

end RothschildStein.P2

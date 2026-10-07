-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationAbsorb
public import RothschildStein.P2.SobolevInterpolationCutoff

/-!
# Sobolev interpolation: seminorm absorption on the `ρ`-balls `U_r^ρ`

The family `U_r^ρ = {ξ ∈ U | ν(Θ(ξ₀, ξ)) < r}` of the radial cutoff construction, as open sets (`rhoOpens`) and the cutoffs
`radialCutoff C ν ξ₀ (σ r) (σ' r)` between `U_{σ r}^ρ` and `U_{σ' r}^ρ` (radial cutoff construction,
`exists_radialCutoff`) with derivative bounds `|X̃_I φ| ≤ C_I (t - s)^{-|I|}` give a
`CutoffFamily` (`exists_cutoffFamily`), so that `seminormPhi_absorption` applies to the `ρ`-balls
(`exists_seminormAbsorption_rho`). (BB pp. 578-583.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

variable {n q s m : ℕ} {w : Fin (q + 1) → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The `ρ`-ball `U_r^ρ` as an open set. -/
def rhoOpens (C : LiftedChart w s Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) (r : ℝ) : Opens (Fin (n + m) → ℝ) :=
  ⟨rhoBall C ν ξ₀ r, isOpen_rhoBall_of C ν hξ₀ r⟩

theorem rhoOpens_mono (C : LiftedChart w s Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {a b : ℝ} (hab : a ≤ b) :
    rhoOpens C ν hξ₀ a ≤ rhoOpens C ν hξ₀ b :=
  fun _ hx => ⟨hx.1, hx.2.trans_le hab⟩

variable (C : LiftedChart w s Ω hΩ X x₀ m)

/-- **The cutoff family of the `ρ`-balls**: there are `r_* ∈ (0, 1]` and
`B ≥ 0` such that for `0 < r < r_*` the radial cutoffs between `U_{σ r}^ρ` and
`U_{σ' r}^ρ` (`σ ∈ [1/2, 1)`, `σ' = (1 + σ)/2`) form a `CutoffFamily` with constant `B`. -/
theorem exists_cutoffFamily (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) :
    ∃ rstar B : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 < r → r < rstar →
      CutoffFamily C.Xl (rhoOpens C ν hξ₀) r B := by
  obtain ⟨rstar, hr0, hr1, hq, hsup⟩ := exists_radialCutoff C ν hν (Kc := {ξ₀})
    isCompact_singleton (by simpa using hξ₀)
  choose C1 hC10 hC1 using fun l : Fin q => hsup [l.succ]
  choose C2 hC20 hC2 using fun l : Fin q => hsup [l.succ, l.succ]
  obtain ⟨C0, hC00, hC0⟩ := hsup [0]
  set B : ℝ := ∑ l : Fin q, C1 l + ∑ l : Fin q, C2 l + C0 with hB
  have hB0 : 0 ≤ B := add_nonneg (add_nonneg (Finset.sum_nonneg fun l _ => hC10 l)
    (Finset.sum_nonneg fun l _ => hC20 l)) hC00
  have hC1B : ∀ l, C1 l ≤ B := fun l => by
    have h1 : C1 l ≤ ∑ l : Fin q, C1 l :=
      Finset.single_le_sum (f := C1) (fun l _ => hC10 l) (Finset.mem_univ l)
    have h2 : 0 ≤ ∑ l : Fin q, C2 l := Finset.sum_nonneg fun l _ => hC20 l
    linarith
  have hC2B : ∀ l, C2 l ≤ B := fun l => by
    have h1 : C2 l ≤ ∑ l : Fin q, C2 l :=
      Finset.single_le_sum (f := C2) (fun l _ => hC20 l) (Finset.mem_univ l)
    have h2 : 0 ≤ ∑ l : Fin q, C1 l := Finset.sum_nonneg fun l _ => hC10 l
    linarith
  have hC0B : C0 ≤ B := by
    have h1 : 0 ≤ ∑ l : Fin q, C1 l := Finset.sum_nonneg fun l _ => hC10 l
    have h2 : 0 ≤ ∑ l : Fin q, C2 l := Finset.sum_nonneg fun l _ => hC20 l
    linarith
  refine ⟨rstar, B, hr0, hr1, hB0, fun r hr hrr σ hσ => ?_⟩
  have hσ1 : σ < 1 := hσ.2
  have hσ2 : 1 / 2 ≤ σ := hσ.1
  set σ' : ℝ := (1 + σ) / 2 with hσ'
  have hs : 0 < σ * r := mul_pos (by linarith) hr
  have hst : σ * r < σ' * r := mul_lt_mul_of_pos_right (by rw [hσ']; linarith) hr
  have htr : σ' * r < rstar := lt_of_le_of_lt
    (by nlinarith [show σ' ≤ 1 by rw [hσ']; linarith]) hrr
  have hdiff : σ' * r - σ * r = (1 - (1 + σ) / 2) * r := by rw [hσ']; ring
  obtain ⟨hcd, hcs, hrange, heq, hts, hcl⟩ := hq ξ₀ (mem_singleton _) (σ * r) (σ' * r) hs hst htr
  set φf : (Fin (n + m) → ℝ) → ℝ := radialCutoff C ν ξ₀ (σ * r) (σ' * r) with hφf
  have htsub : tsupport φf ⊆ (rhoOpens C ν hξ₀ r : Set (Fin (n + m) → ℝ)) := by
    intro x hx
    have h1 := hcl (hts hx)
    have h2 : rhoBall C ν ξ₀ (σ' * r) ⊆ rhoBall C ν ξ₀ r := fun y hy =>
      ⟨hy.1, hy.2.trans_le (by nlinarith [show σ' ≤ 1 by rw [hσ']; linarith])⟩
    exact h2 h1
  let φ : TestFunction (rhoOpens C ν hξ₀ r) ℝ (⊤ : ℕ∞) := ⟨φf, hcd, hcs, htsub⟩
  have hφc : (φ : (Fin (n + m) → ℝ) → ℝ) = φf := rfl
  have hts' : tsupport φf ⊆ (rhoOpens C ν hξ₀ (σ' * r) : Set (Fin (n + m) → ℝ)) :=
    fun x hx => hcl (hts hx)
  have hhpos : 0 < (1 - (1 + σ) / 2) * r := mul_pos (by linarith) hr
  -- the weighted bounds
  have hzp : ∀ (y : ℝ) (k : ℕ), y ^ (-(k : ℤ)) = (y ^ k)⁻¹ := fun y k => by
    rw [zpow_neg, zpow_natCast]
  have b1 : ∀ (l : Fin q) (x : Fin (n + m) → ℝ),
      |fieldDerivative (C.Xl l.succ) φf x| ≤ B / ((1 - (1 + σ) / 2) * r) := by
    intro l x
    have h := hC1 l ξ₀ (mem_singleton _) (σ * r) (σ' * r) hs hst htr x
    have hw1 : wordWeight w [l.succ] = 1 := by simp [wordWeight, hw l]
    rw [hw1, hdiff] at h
    have e : fieldDerivative (C.Xl l.succ) φf x = wordDerivative C.Xl [l.succ] φf x := rfl
    rw [e]
    refine h.trans ?_
    rw [hzp, pow_one, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hC1B l) hhpos.le
  have b2 : ∀ (l : Fin q) (x : Fin (n + m) → ℝ),
      |fieldDerivative (C.Xl l.succ) (fieldDerivative (C.Xl l.succ) φf) x| ≤
        B / ((1 - (1 + σ) / 2) * r) ^ 2 := by
    intro l x
    have h := hC2 l ξ₀ (mem_singleton _) (σ * r) (σ' * r) hs hst htr x
    have hw2 : wordWeight w [l.succ, l.succ] = 2 := by simp [wordWeight, hw l]
    rw [hw2, hdiff] at h
    have e : fieldDerivative (C.Xl l.succ) (fieldDerivative (C.Xl l.succ) φf) x =
        wordDerivative C.Xl [l.succ, l.succ] φf x := rfl
    rw [e]
    refine h.trans ?_
    rw [hzp, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hC2B l) (by positivity)
  have b0 : ∀ x : Fin (n + m) → ℝ, |fieldDerivative (C.Xl 0) φf x| ≤
      B / ((1 - (1 + σ) / 2) * r) ^ 2 := by
    intro x
    have h := hC0 ξ₀ (mem_singleton _) (σ * r) (σ' * r) hs hst htr x
    have hw2 : wordWeight w [0] = 2 := by simp [wordWeight, hw0]
    rw [hw2, hdiff] at h
    have e : fieldDerivative (C.Xl 0) φf x = wordDerivative C.Xl [0] φf x := rfl
    rw [e]
    refine h.trans ?_
    rw [hzp, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hC0B (by positivity)
  exact ⟨φ, fun x => (hrange x).1, fun x => (hrange x).2, fun x hx => heq hx, hts', b1, b2, b0⟩

end RothschildStein.P2

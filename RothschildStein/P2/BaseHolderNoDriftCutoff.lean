-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderNoDriftCompact
public import RothschildStein.P2.Cutoffs

/-!
# No drift: the cutoff data of the radial cutoff construction in sup and Hölder form

From the radial cutoff construction (BB Cor 11.37, pp. 579–580), alphabet `Fin q`, all weights one. At one chart centre `ξ₀ ∈ U`, for
`0 < s < r < r_*` the radial cutoff `ζ = φ(s, r)` is smooth with compact support, `0 ≤ ζ ≤ 1`, `ζ = 1` on `U_s^ρ`,
`tsupport ζ ⊆ U_r^ρ`, and (`g = r - s`)

* sup bounds `|X̃ᵢ ζ| ≤ b₁ g⁻¹`, `|L̃ ζ| ≤ b₂ g⁻²`;
* Hölder bounds `‖ζ‖_{C^α} ≤ B₀ g⁻¹`, `‖X̃ᵢ ζ‖_{C^α} ≤ B₁ g⁻²`, `‖L̃ ζ‖_{C^α} ≤ B₂ g⁻³` on the chart domain `O`
  (`L̃ ζ = ∑ᵢ X̃ᵢ² ζ`, the Hölder norm of a finite sum is the sum of the norms).

`CutoffDataNoDrift` records this package and `exists_cutoffData_noDrift` produces it from `smooth_cutoffs_noDrift`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The cutoff package at the centre `ξ₀` for the radii below `rstar`: smoothness, support, the sup
bounds `b₁, b₂` and the Hölder bounds `B₀, B₁, B₂` of `ζ`, `X̃ᵢ ζ`, `L̃ ζ`. -/
structure CutoffDataNoDrift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) (α rstar b₁ b₂ B₀ B₁ B₂ : ℝ) : Prop where
  smooth : ∀ s r : ℝ, 0 < s → s < r → r < rstar → ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ s r)
  compact : ∀ s r : ℝ, 0 < s → s < r → r < rstar → HasCompactSupport (radialCutoff C ν ξ₀ s r)
  range : ∀ s r : ℝ, 0 < s → s < r → r < rstar → ∀ ξ,
    0 ≤ radialCutoff C ν ξ₀ s r ξ ∧ radialCutoff C ν ξ₀ s r ξ ≤ 1
  eq_one : ∀ s r : ℝ, 0 < s → s < r → r < rstar →
    EqOn (radialCutoff C ν ξ₀ s r) (fun _ => 1) (rhoBall C ν ξ₀ s)
  support : ∀ s r : ℝ, 0 < s → s < r → r < rstar →
    tsupport (radialCutoff C ν ξ₀ s r) ⊆ rhoBall C ν ξ₀ r
  deriv1 : ∀ s r : ℝ, 0 < s → s < r → r < rstar → ∀ (i : Fin q) (ξ : Fin (n + m) → ℝ),
    |fieldDerivative (C.Xl i) (radialCutoff C ν ξ₀ s r) ξ| ≤ b₁ * (r - s)⁻¹
  deriv2 : ∀ s r : ℝ, 0 < s → s < r → r < rstar → ∀ ξ : Fin (n + m) → ℝ,
    |sumSquares C.Xl (radialCutoff C ν ξ₀ s r) ξ| ≤ b₂ * ((r - s) ^ 2)⁻¹
  holder0 : ∀ s r : ℝ, 0 < s → s < r → r < rstar →
    holderENorm C.dl α C.O (radialCutoff C ν ξ₀ s r) ≤ ENNReal.ofReal (B₀ * (r - s)⁻¹)
  holder1 : ∀ s r : ℝ, 0 < s → s < r → r < rstar → ∀ i : Fin q,
    holderENorm C.dl α C.O (fieldDerivative (C.Xl i) (radialCutoff C ν ξ₀ s r)) ≤
      ENNReal.ofReal (B₁ * ((r - s) ^ 2)⁻¹)
  holder2 : ∀ s r : ℝ, 0 < s → s < r → r < rstar →
    holderENorm C.dl α C.O (sumSquares C.Xl (radialCutoff C ν ξ₀ s r)) ≤
      ENNReal.ofReal (B₂ * ((r - s) ^ 3)⁻¹)

/-- **The cutoff package, no drift** (BB Cor 11.37, pp. 579-580): at every chart centre `ξ₀ ∈ U`, for every
`0 < α < 1` there are `r_* ∈ (0, 1]` and nonnegative constants `b₁, b₂, B₀, B₁, B₂`. -/
theorem exists_cutoffData_noDrift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ rstar b₁ b₂ B₀ B₁ B₂ : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧ 0 ≤ b₁ ∧ 0 ≤ b₂ ∧ 0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      CutoffDataNoDrift C ν ξ₀ α rstar b₁ b₂ B₀ B₁ B₂ := by
  classical
  obtain ⟨rstar, hr0, hr1, hq, hsup, hhol⟩ := smooth_cutoffs_noDrift C ν hν
    (isCompact_singleton (x := ξ₀)) (singleton_subset_iff.2 hξ₀)
  have w0 : wordWeight noDriftWeight ([] : List (Fin q)) = 0 := rfl
  have w1 : ∀ i : Fin q, wordWeight noDriftWeight [i] = 1 := fun i => by
    simp [wordWeight, noDriftWeight]
  have w2 : ∀ i : Fin q, wordWeight noDriftWeight [i, i] = 2 := fun i => by
    simp [wordWeight, noDriftWeight]
  choose C1 hC1 hC1b using fun i : Fin q => hsup [i]
  choose C2 hC2 hC2b using fun i : Fin q => hsup [i, i]
  obtain ⟨H0, hH0, hH0b⟩ := hhol []
  choose H1 hH1 hH1b using fun i : Fin q => hhol [i]
  choose H2 hH2 hH2b using fun i : Fin q => hhol [i, i]
  refine ⟨rstar, ∑ i, C1 i, ∑ i, C2 i, H0, ∑ i, H1 i, ∑ i, H2 i, hr0, hr1,
    Finset.sum_nonneg fun i _ => hC1 i, Finset.sum_nonneg fun i _ => hC2 i, hH0,
    Finset.sum_nonneg fun i _ => hH1 i, Finset.sum_nonneg fun i _ => hH2 i, ?_⟩
  have hmem : ξ₀ ∈ ({ξ₀} : Set (Fin (n + m) → ℝ)) := mem_singleton _
  refine ⟨fun s r hs hsr hr => (hq ξ₀ hmem s r hs hsr hr).1,
    fun s r hs hsr hr => (hq ξ₀ hmem s r hs hsr hr).2.1,
    fun s r hs hsr hr => (hq ξ₀ hmem s r hs hsr hr).2.2.1,
    fun s r hs hsr hr => (hq ξ₀ hmem s r hs hsr hr).2.2.2.1,
    fun s r hs hsr hr => ((hq ξ₀ hmem s r hs hsr hr).2.2.2.2.1).trans
      (((hq ξ₀ hmem s r hs hsr hr).2.2.2.2.2)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro s r hs hsr hr i ξ
    have h := hC1b i ξ₀ hmem s r hs hsr hr ξ
    rw [w1 i] at h
    have e : (r - s) ^ (-((1 : ℕ) : ℤ)) = (r - s)⁻¹ := by simp
    rw [e] at h
    have hle : C1 i ≤ ∑ j, C1 j :=
      Finset.single_le_sum (f := C1) (fun j _ => hC1 j) (Finset.mem_univ i)
    have hpos : 0 ≤ (r - s)⁻¹ := inv_nonneg.2 (sub_pos.2 hsr).le
    exact h.trans (mul_le_mul_of_nonneg_right hle hpos)
  · intro s r hs hsr hr ξ
    have e : (r - s) ^ (-((2 : ℕ) : ℤ)) = ((r - s) ^ 2)⁻¹ := by simp [zpow_neg]
    have hi : ∀ i : Fin q, |wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ| ≤
        C2 i * ((r - s) ^ 2)⁻¹ := fun i => by
      have h := hC2b i ξ₀ hmem s r hs hsr hr ξ
      rw [w2 i, e] at h
      exact h
    have hL : sumSquares C.Xl (radialCutoff C ν ξ₀ s r) ξ =
        ∑ i : Fin q, wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ := rfl
    rw [hL]
    calc |∑ i : Fin q, wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ|
        ≤ ∑ i : Fin q, |wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin q, C2 i * ((r - s) ^ 2)⁻¹ := Finset.sum_le_sum fun i _ => hi i
      _ = (∑ i, C2 i) * ((r - s) ^ 2)⁻¹ := by rw [Finset.sum_mul]
  · intro s r hs hsr hr
    have h := hH0b ξ₀ hmem s r hs hsr hr α hα0 hα1
    rw [w0] at h
    have e : (r - s) ^ (-((0 : ℕ) + 1 : ℤ)) = (r - s)⁻¹ := by simp
    rw [e] at h
    exact h
  · intro s r hs hsr hr i
    have h := hH1b i ξ₀ hmem s r hs hsr hr α hα0 hα1
    rw [w1 i] at h
    have e : (r - s) ^ (-(((1 : ℕ) : ℤ) + 1)) = ((r - s) ^ 2)⁻¹ := by
      rw [show -(((1 : ℕ) : ℤ) + 1) = -((2 : ℕ) : ℤ) by norm_num]
      simp [zpow_neg]
    rw [e] at h
    have hle : H1 i ≤ ∑ j, H1 j :=
      Finset.single_le_sum (f := H1) (fun j _ => hH1 j) (Finset.mem_univ i)
    have hpos : 0 ≤ ((r - s) ^ 2)⁻¹ := by positivity
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle hpos))
  · intro s r hs hsr hr
    have e : (r - s) ^ (-(((2 : ℕ) : ℤ) + 1)) = ((r - s) ^ 3)⁻¹ := by
      rw [show -(((2 : ℕ) : ℤ) + 1) = -((3 : ℕ) : ℤ) by norm_num]
      simp [zpow_neg]
    have hi : ∀ i : Fin q, holderENorm C.dl α C.O
        (wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r)) ≤
          ENNReal.ofReal (H2 i * ((r - s) ^ 3)⁻¹) := fun i => by
      have h := hH2b i ξ₀ hmem s r hs hsr hr α hα0 hα1
      rw [w2 i, e] at h
      exact h
    have hL : sumSquares C.Xl (radialCutoff C ν ξ₀ s r) =
        fun ξ => ∑ i : Fin q, wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ := rfl
    rw [hL]
    have hpos : 0 ≤ ((r - s) ^ 3)⁻¹ := by
      have : 0 < r - s := sub_pos.2 hsr
      positivity
    calc _ ≤ ∑ i : Fin q, holderENorm C.dl α C.O
          (wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r)) :=
          holderENorm_finset_sum_le hα0.le _ _
      _ ≤ ∑ i : Fin q, ENNReal.ofReal (H2 i * ((r - s) ^ 3)⁻¹) := Finset.sum_le_sum fun i _ => hi i
      _ = ENNReal.ofReal (∑ i : Fin q, H2 i * ((r - s) ^ 3)⁻¹) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          exact fun i _ => mul_nonneg (hH2 i) hpos
      _ = _ := by rw [Finset.sum_mul]

end RothschildStein.P2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderProduct
public import RothschildStein.P2.ProductAbsorptionFamily

/-!
# Radial cutoff data used by the cutoff estimate

For the cutoff estimate (BB p. 601, (11.92)). For the radial cutoff `ζ = φ(t, s)` of the radial cutoff
construction
(`ζ = 1` on `U_t^ρ`, `tsupport ζ ⊆ closedρ((t + s)/2) ⊆ U_s^ρ`) and `a = s - t`, `A = a⁻¹`:

* `‖ζ‖_{C^α} ≤ C_b A`, `‖X̃_l ζ‖_{C^α} ≤ C_b A²` (Hölder norms for the lifted control distance);
* `|L̃ζ| ≤ C_b A²`, `|X̃_l L̃ζ| ≤ C_b A³`, `|L̃ L̃ζ| ≤ C_b A⁴`,

with one constant `C_b` and threshold `r_* ≤ 1` for all `0 < t < s < r_*` (`exists_cutoffData`). The sup
bounds of `L̃ζ` and its first and second derivatives come from the radial cutoff bounds of the words of length at
most four (`X̃_I L̃ζ = ∑ X̃_{I w} ζ` over the `q + 1` words `w` of weight two).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {N q : ℕ}

/-- `L̃ ζ = ∑_{w} X̃_w ζ` over the `q + 1` words of weight two (functions). -/
theorem sumSquaresWithDrift_eq_sum_weightTwo (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (ζ : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) :
    sumSquaresWithDrift X ζ z = ∑ i : Fin (q + 1), wordDerivative X (weightTwoWord i) ζ z := by
  rw [sumSquaresWithDrift_eq_listSum]
  beta_reduce
  rw [← Fin.sum_univ_def]

/-- Pointwise bound of the word derivatives of `L̃ ζ`:
`|X̃_I L̃ζ (z)| ≤ (q + 1) C_b a^{-(wt I + 2)}` for words `I` of length at most two, from the radial cutoff bounds of
the words `I ++ w` of length at most four. -/
theorem abs_wordDerivative_sumSquares_le (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (V : Opens (Fin N → ℝ)) (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin N → ℝ)))
    {ζ : (Fin N → ℝ) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) {O : Set (Fin N → ℝ)} {α a : ℝ}
    {c : List (Fin (q + 1)) → ℝ} (hP : RadialCutoffBounds X O α a ζ c) {Cb0 : ℝ}
    (hc : ∀ I : List (Fin (q + 1)), I.length ≤ 4 → c I ≤ Cb0) (ha : 0 < a)
    (I : List (Fin (q + 1))) (hI : I.length ≤ 2) {z : Fin N → ℝ} (hz : z ∈ (V : Set (Fin N → ℝ))) :
    |wordDerivative X I (sumSquaresWithDrift X ζ) z| ≤
      ((q : ℝ) + 1) * Cb0 * (a⁻¹) ^ (wordWeight driftWeight I + 2) := by
  have hzpow : ∀ e : ℤ, 0 ≤ a ^ e := fun e => zpow_nonneg ha.le e
  have hterm : ∀ i : Fin (q + 1), |wordDerivative X (I ++ weightTwoWord i) ζ z| ≤
      Cb0 * (a⁻¹) ^ (wordWeight driftWeight I + 2) := by
    intro i
    refine (hP.sup (I ++ weightTwoWord i) z).trans ?_
    have hlen : (I ++ weightTwoWord i).length ≤ 4 := by
      have := weightTwoWord_length i
      simp only [List.length_append]
      omega
    have hexp : a ^ (-((wordWeight driftWeight (I ++ weightTwoWord i) : ℕ) : ℤ)) =
        (a⁻¹) ^ (wordWeight driftWeight I + 2) := by
      rw [wordWeight_append_eq, wordWeight_weightTwoWord, zpow_neg, zpow_natCast, inv_pow]
    rw [hexp]
    exact mul_le_mul_of_nonneg_right (hc _ hlen) (pow_nonneg (inv_nonneg.2 ha.le) _)
  rw [wordDerivative_sumSquaresWithDrift X V hXV hζ.contDiffOn I hz]
  calc |∑ i : Fin (q + 1), wordDerivative X (I ++ weightTwoWord i) ζ z|
      ≤ ∑ i : Fin (q + 1), |wordDerivative X (I ++ weightTwoWord i) ζ z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (q + 1), Cb0 * (a⁻¹) ^ (wordWeight driftWeight I + 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ((q : ℝ) + 1) * Cb0 * (a⁻¹) ^ (wordWeight driftWeight I + 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

variable {n st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The lifted fields are smooth on the chart domain `C.U`. -/
theorem liftedChart_contDiffOn_Xl_U (C : LiftedChart driftWeight st Ω hΩ X x₀ m) (i : Fin (q + 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) C.U :=
  (C.lift_smooth i).mono fun _ hξ => C.closure_U_subset (subset_closure hξ)

/-- **Radial cutoff data.** For a smooth gauge `ν` and a centre `ξ₀ ∈ C.U`
there are `r_* ∈ (0, 1]` and `C_b ≥ 0` such that for `0 < t < s < r_*` the radial cutoff
`ζ = radialCutoff C ν ξ₀ t s` is smooth with compact support, `0 ≤ ζ ≤ 1`, `ζ = 1` on `U_t^ρ`,
`tsupport ζ ⊆ closedρ((t + s)/2) ⊆ U_s^ρ`, and with `A = (s - t)⁻¹` its Hölder norms and the sup bounds of
`L̃ζ` and its derivatives are as listed in the module docstring. -/
theorem exists_cutoffData (C : LiftedChart driftWeight st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ rstar Cb : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧ 0 ≤ Cb ∧ ∀ t s : ℝ, 0 < t → t < s → s < rstar →
      ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ t s) ∧
      HasCompactSupport (radialCutoff C ν ξ₀ t s) ∧
      (∀ ξ, 0 ≤ radialCutoff C ν ξ₀ t s ξ ∧ radialCutoff C ν ξ₀ t s ξ ≤ 1) ∧
      EqOn (radialCutoff C ν ξ₀ t s) (fun _ => 1) (rhoBall C ν ξ₀ t) ∧
      tsupport (radialCutoff C ν ξ₀ t s) ⊆ closedRhoBall C ν ξ₀ ((t + s) / 2) ∧
      closedRhoBall C ν ξ₀ ((t + s) / 2) ⊆ rhoBall C ν ξ₀ s ∧
      holderENorm C.dl α C.O (radialCutoff C ν ξ₀ t s) ≤ ENNReal.ofReal (Cb * (s - t)⁻¹) ∧
      (∀ l : Fin q, holderENorm C.dl α C.O (fieldDerivative (C.Xl l.succ) (radialCutoff C ν ξ₀ t s)) ≤
        ENNReal.ofReal (Cb * (s - t)⁻¹ ^ 2)) ∧
      (∀ ξ, |sumSquaresWithDrift C.Xl (radialCutoff C ν ξ₀ t s) ξ| ≤ Cb * (s - t)⁻¹ ^ 2) ∧
      (∀ (l : Fin q) ξ, |fieldDerivative (C.Xl l.succ)
        (sumSquaresWithDrift C.Xl (radialCutoff C ν ξ₀ t s)) ξ| ≤ Cb * (s - t)⁻¹ ^ 3) ∧
      (∀ ξ, |sumSquaresWithDrift C.Xl (sumSquaresWithDrift C.Xl (radialCutoff C ν ξ₀ t s)) ξ| ≤
        Cb * (s - t)⁻¹ ^ 4) := by
  classical
  obtain ⟨rstar, hr0, hr1, c, Cb0, hc, hmain⟩ := exists_radialCutoffBounds_of_smooth_cutoffs_drift C ν hν
    (isCompact_singleton (x := ξ₀)) (singleton_subset_iff.2 hξ₀)
  set Cb0' : ℝ := max Cb0 0 with hCb0'
  have hCb0'0 : 0 ≤ Cb0' := le_max_right _ _
  have hc' : ∀ I : List (Fin (q + 1)), I.length ≤ 4 → c I ≤ Cb0' := fun I hI =>
    (hc I hI).trans (le_max_left _ _)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  set Cb : ℝ := ((q : ℝ) + 1) ^ 2 * Cb0' with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  have hCb1 : Cb0' ≤ Cb := by
    have : 1 ≤ ((q : ℝ) + 1) ^ 2 := one_le_pow₀ hq1
    nlinarith
  have hCb2 : ((q : ℝ) + 1) * Cb0' ≤ Cb := by
    have : (q : ℝ) + 1 ≤ ((q : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  refine ⟨rstar, Cb, hr0, hr1, hCb0, ?_⟩
  intro t s ht hts hs
  obtain ⟨hqual, hbd⟩ := hmain ξ₀ (mem_singleton _) t s ht hts hs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hqual
  have hP := hbd α hα0 hα1
  have ha : 0 < s - t := sub_pos.2 hts
  set ζ := radialCutoff C ν ξ₀ t s with hζ
  have hA0 : 0 ≤ (s - t)⁻¹ := inv_nonneg.2 ha.le
  have hsuppU : tsupport ζ ⊆ C.U := h5.trans fun ξ hξ => hξ.1
  have hzpow : ∀ k : ℕ, (s - t) ^ (-((k : ℕ) : ℤ)) = ((s - t)⁻¹) ^ k := fun k => by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (C.chartOpens : Set (Fin (n + m) → ℝ)) := fun i =>
    liftedChart_contDiffOn_Xl_U C i
  have hsubL : tsupport (sumSquaresWithDrift C.Xl ζ) ⊆ tsupport ζ :=
    tsupport_sumSquaresWithDrift_subset C.Xl ζ
  have hsubLL : tsupport (sumSquaresWithDrift C.Xl (sumSquaresWithDrift C.Xl ζ)) ⊆ tsupport ζ :=
    (tsupport_sumSquaresWithDrift_subset C.Xl _).trans hsubL
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, ?_⟩
  · have := hP.holder []
    have e : (s - t) ^ (-((wordWeight driftWeight ([] : List (Fin (q + 1))) : ℤ) + 1)) =
        (s - t)⁻¹ ^ 1 := by
      have := hzpow 1
      simp [wordWeight]
    rw [e] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right ((hc' [] (by simp)).trans hCb1) hA0
  · intro l
    have := hP.holder [l.succ]
    have e : (s - t) ^ (-((wordWeight driftWeight [l.succ] : ℤ) + 1)) = (s - t)⁻¹ ^ 2 := by
      have := hzpow 2
      rw [wordWeight_single_succ]
      simp
    rw [e] at this
    exact this.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right ((hc' _ (by simp)).trans hCb1) (pow_nonneg hA0 _)))
  · intro ξ
    by_cases hξ : ξ ∈ C.U
    · have := abs_wordDerivative_sumSquares_le C.Xl C.chartOpens hXV h1 hP hc' ha [] (by simp) hξ
      simp only [wordWeight, List.map_nil, List.sum_nil, zero_add] at this
      refine (show |sumSquaresWithDrift C.Xl ζ ξ| ≤ _ from this).trans ?_
      exact mul_le_mul_of_nonneg_right hCb2 (pow_nonneg hA0 _)
    · have hz : ξ ∉ tsupport (sumSquaresWithDrift C.Xl ζ) := fun h => hξ (hsuppU (hsubL h))
      rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
      positivity
  · intro l ξ
    by_cases hξ : ξ ∈ C.U
    · have := abs_wordDerivative_sumSquares_le C.Xl C.chartOpens hXV h1 hP hc' ha [l.succ]
        (by simp) hξ
      rw [wordWeight_single_succ] at this
      refine (show |fieldDerivative (C.Xl l.succ) (sumSquaresWithDrift C.Xl ζ) ξ| ≤ _ from this).trans
        ?_
      exact mul_le_mul_of_nonneg_right hCb2 (pow_nonneg hA0 _)
    · have hz : ξ ∉ tsupport (sumSquaresWithDrift C.Xl ζ) := fun h => hξ (hsuppU (hsubL h))
      rw [fieldDerivative_eq_zero_of_notMem_tsupport hz, abs_zero]
      positivity
  · intro ξ
    by_cases hξ : ξ ∈ C.U
    · rw [sumSquaresWithDrift_eq_sum_weightTwo]
      have hk : ∀ k : Fin (q + 1), |wordDerivative C.Xl (weightTwoWord k)
          (sumSquaresWithDrift C.Xl ζ) ξ| ≤ ((q : ℝ) + 1) * Cb0' * (s - t)⁻¹ ^ 4 := by
        intro k
        have := abs_wordDerivative_sumSquares_le C.Xl C.chartOpens hXV h1 hP hc' ha (weightTwoWord k)
          (weightTwoWord_length k) hξ
        rw [wordWeight_weightTwoWord] at this
        exact this
      calc |∑ k : Fin (q + 1), wordDerivative C.Xl (weightTwoWord k) (sumSquaresWithDrift C.Xl ζ) ξ|
          ≤ ∑ k : Fin (q + 1), |wordDerivative C.Xl (weightTwoWord k)
            (sumSquaresWithDrift C.Xl ζ) ξ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin (q + 1), ((q : ℝ) + 1) * Cb0' * (s - t)⁻¹ ^ 4 :=
            Finset.sum_le_sum fun k _ => hk k
        _ = Cb * (s - t)⁻¹ ^ 4 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [hCb]
            push_cast
            ring
    · have hz : ξ ∉ tsupport (sumSquaresWithDrift C.Xl (sumSquaresWithDrift C.Xl ζ)) := fun h =>
        hξ (hsuppU (hsubLL h))
      rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
      positivity

end RothschildStein.P2

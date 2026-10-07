-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesDerivative
public import RothschildStein.P1.KernelEstimatesPath

/-!
# First-variable difference bound

For `K(ξ, η) = Ψ(ξ, η, Θ(η, ξ))` with weighted bounds, uniformly for `ξ, ξ', η` in a compact
`K₀ ⊆ U` and `d̃(ξ', η) > 2 d̃(ξ, ξ')`:
`|K(ξ', η) - K(ξ, η)| ≤ B d̃(ξ, ξ') d̃(ξ', η)^(d - 1)`.

Near separations (`d̃(ξ, ξ') < d̃(ξ', η) / 4`, small parameter) the mean value inequality along a
controlled curve of parameter `< 2 d̃(ξ, ξ')` is integrated against the derivative bounds; the path
margin keeps the curve in a compact neighborhood of `K₀` at pole distance between `r / 2` and
`3 r / 2`. In the remaining cases the endpoint size bounds suffice
(BB pp. 569–571, Prop 11.32; [GAP-FILL: path margins]).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
open scoped BigOperators ENNReal
namespace RothschildStein.P1

/-- A controlled curve of the domain `Ω` that stays in a smaller set `Ω'` is a controlled
curve of `Ω'` (the same measurable controls). -/
theorem isControlledCurve_restrict {m n : ℕ} {Ω Ω' : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) (hΩ' : MapsTo γ (Icc (0 : ℝ) 1) Ω') :
    isControlledCurve Ω' w X δ γ :=
  ⟨hγ.1, hγ.2.1, hΩ', hγ.2.2.2⟩

/-- Weight comparison along a curve: for `0 < δ ≤ r` and a weight `w ≥ 1`,
`δ^w r^(d - w) ≤ δ r^(d - 1)`. -/
theorem pow_mul_zpow_le {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (d : ℤ) {a : ℕ} (ha : 0 < a) :
    δ ^ a * r ^ (d - (a : ℤ)) ≤ δ * r ^ (d - 1) := by
  have hr : 0 < r := hδ.trans_le hδr
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h1 : δ ^ b ≤ r ^ b := pow_le_pow_left₀ hδ.le hδr b
  have h2 : r ^ (d - ((b + 1 : ℕ) : ℤ)) * r ^ b = r ^ (d - 1) := by
    rw [← zpow_natCast, ← zpow_add₀ hr.ne']
    congr 1
    push_cast
    ring
  calc δ ^ (b + 1) * r ^ (d - ((b + 1 : ℕ) : ℤ))
      = δ * (δ ^ b * r ^ (d - ((b + 1 : ℕ) : ℤ))) := by ring
    _ ≤ δ * (r ^ b * r ^ (d - ((b + 1 : ℕ) : ℤ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (zpow_pos hr _).le) hδ.le
    _ = δ * r ^ (d - 1) := by rw [mul_comm (r ^ b), h2]

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)
variable {Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {d : ℤ}

/-- Mean value along a controlled curve at pole distance comparable to `r`: if a controlled
curve of parameter `δ ≤ r` stays in a compact `L ⊆ U` with `r / 2 ≤ d̃(γ t, η) ≤ 2 r`, then
`|K(γ 1, η) - K(γ 0, η)| ≤ B₁ δ r^(d - 1)` (BB p. 570). -/
theorem exists_path_difference_bound (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hWB : HasWeightedBounds C.G d Ψ) {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLU : L ⊆ C.U) :
    ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∀ η ∈ L, ∀ δ r : ℝ, 0 < δ → δ ≤ r → ∀ γ : ℝ → (Fin (n + m) → ℝ),
      isControlledCurve C.O w C.Xl δ γ → (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ L) →
      (∀ t ∈ Icc (0 : ℝ) 1, r / 2 ≤ (C.dl (γ t) η).toReal ∧ (C.dl (γ t) η).toReal ≤ 2 * r) →
      |Ψ (γ 1) η (C.Θ η (γ 1)) - Ψ (γ 0) η (C.Θ η (γ 0))| ≤ B₁ * (δ * r ^ (d - 1)) := by
  choose M hM0 hM using fun i => C.exists_derivative_bound hΨ hWB hL hLU i
  refine ⟨∑ i, M i * 2 ^ (d - ((w i : ℕ) : ℤ)).natAbs, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hM0 i) (by positivity))
  intro η hη δ r hδ hδr γ hγ hγL hγd
  have hr : 0 < r := hδ.trans_le hδr
  have hηU := hLU hη
  have hpole : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ η := by
    intro t ht h
    have := (hγd t ht).1
    rw [h, (C.dl_eq_zero_iff hηU hηU).mpr rfl, ENNReal.toReal_zero] at this
    linarith
  have hΩ' : IsOpen (C.U \ {η}) := C.isOpen_U.sdiff isClosed_singleton
  have hmaps : MapsTo γ (Icc (0 : ℝ) 1) (C.U \ {η}) :=
    fun t ht => ⟨hLU (hγL t ht), hpole t ht⟩
  have hγ' : isControlledCurve (C.U \ {η}) w C.Xl δ γ := isControlledCurve_restrict hγ hmaps
  refine (RothschildStein.G1.controlledCurve_variation_le hΩ' (C.kernel_contDiffOn hΨ hηU) hγ'
    (C := ∑ i, δ ^ (w i : ℕ) * (M i * (2 ^ (d - ((w i : ℕ) : ℤ)).natAbs *
      r ^ (d - ((w i : ℕ) : ℤ))))) ?_).trans ?_
  · intro t ht
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hz := hγL t ht
    have hb := hM i η hη (γ t) hz (hpole t ht)
    have hx := (hγd t ht)
    have hxpos : 0 < (C.dl (γ t) η).toReal := by linarith [hx.1]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (hM0 i))
    exact kzpow_le_const_mul (by norm_num : (1 : ℝ) ≤ 2) hxpos hr (by linarith [hx.2])
      (by linarith [hx.1]) _
  · rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h1 := pow_mul_zpow_le hδ hδr d (w i).pos
    have hc : 0 ≤ M i * 2 ^ (d - ((w i : ℕ) : ℤ)).natAbs :=
      mul_nonneg (hM0 i) (by positivity)
    calc δ ^ (w i : ℕ) * (M i * (2 ^ (d - ((w i : ℕ) : ℤ)).natAbs * r ^ (d - ((w i : ℕ) : ℤ))))
        = M i * 2 ^ (d - ((w i : ℕ) : ℤ)).natAbs *
            (δ ^ (w i : ℕ) * r ^ (d - ((w i : ℕ) : ℤ))) := by ring
      _ ≤ M i * 2 ^ (d - ((w i : ℕ) : ℤ)).natAbs * (δ * r ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left h1 hc

/-- First-variable difference bound (path margin, then intermediate and far poles):
uniformly on a compact `K₀ ⊆ U`, if `d̃(ξ', η) > 2 d̃(ξ, ξ')` then
`|K(ξ', η) - K(ξ, η)| ≤ B d̃(ξ, ξ') d̃(ξ', η)^(d - 1)` (BB pp. 569–571, Prop 11.32, (11.49);
[GAP-FILL: path margins]; no minimizing path is assumed). -/
theorem exists_difference_bound_first (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hWB : HasWeightedBounds C.G d Ψ) {K₀ : Set (Fin (n + m) → ℝ)} (hK₀ : IsCompact K₀)
    (hK₀U : K₀ ⊆ C.U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ ∈ K₀, ∀ ξ' ∈ K₀, ∀ η ∈ K₀,
      2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
      |Ψ ξ' η (C.Θ η ξ') - Ψ ξ η (C.Θ η ξ)| ≤
        B * ((C.dl ξ ξ').toReal * (C.dl ξ' η).toReal ^ (d - 1)) := by
  obtain ⟨ε, hε, hεU, r₁, hr₁, hmargin⟩ := C.exists_path_margin hK₀ hK₀U
  have hLc : IsCompact (cthickening ε K₀) := hK₀.cthickening
  obtain ⟨B₁, hB₁0, hB₁⟩ := C.exists_path_difference_bound hΨ hWB hLc hεU
  obtain ⟨A, hA0, hA⟩ := C.exists_size_bound hWB hK₀ hK₀U
  obtain ⟨R₀, hR₀⟩ := C.exists_gauge_bound hK₀ hK₀U
  set D : ℝ := C.gaugeConst * max R₀ 1 with hD
  have hDpos : 0 < D := mul_pos C.gaugeConst_pos (lt_of_lt_of_le one_pos (le_max_right _ _))
  set c₂ : ℝ := max 4 (2 * D / r₁) with hc₂
  have hc₂0 : 0 ≤ c₂ := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)
  have hAc : 0 ≤ A * (1 + 2 ^ d.natAbs) * c₂ := by positivity
  refine ⟨2 * B₁ + A * (1 + 2 ^ d.natAbs) * c₂, by positivity, ?_⟩
  intro ξ hξ ξ' hξ' η hη hsep
  have hξU := hK₀U hξ
  have hξ'U := hK₀U hξ'
  have hηU := hK₀U hη
  set h : ℝ := (C.dl ξ ξ').toReal with hh
  set r : ℝ := (C.dl ξ' η).toReal with hr
  have hh0 : 0 ≤ h := ENNReal.toReal_nonneg
  have hr0 : 0 < r := by linarith
  have hrd : 0 < r ^ (d - 1) := zpow_pos hr0 _
  have hhr : 0 ≤ h * r ^ (d - 1) := mul_nonneg hh0 hrd.le
  have hhsy : (C.dl ξ' ξ).toReal = h := by rw [C.dl_symm ξ' ξ]
  rcases hh0.eq_or_lt with hz | hpos
  · -- `ξ = ξ'`
    have hdl : C.dl ξ ξ' = 0 := by
      have : (C.dl ξ ξ').toReal = 0 := hz.symm
      rcases (ENNReal.toReal_eq_zero_iff _).mp this with h0 | h0
      · exact h0
      · exact absurd h0 (C.dl_ne_top hξU hξ'U)
    have hee : ξ' = ξ := (C.dl_eq_zero_iff hξU hξ'U).mp hdl
    rw [hee, sub_self, abs_zero]
    exact mul_nonneg (by positivity) hhr
  · by_cases hcase : 4 * h < r ∧ 2 * h < r₁
    · -- path argument
      obtain ⟨hA4, hr1⟩ := hcase
      have hlt : C.dl ξ' ξ < ENNReal.ofReal (2 * h) := by
        have : C.dl ξ' ξ = ENNReal.ofReal h := by
          rw [C.dl_symm ξ' ξ, hh, ENNReal.ofReal_toReal (C.dl_ne_top hξU hξ'U)]
        rw [this]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
      obtain ⟨δ, hδ, hδ2h, γ, hγ, hγ0, hγ1⟩ :=
        RothschildStein.G1.exists_controlledCurve_of_controlDistance_lt hlt
      have hmem := hmargin ξ' hξ' δ (by linarith) γ hγ hγ0
      have hsub : ∀ t ∈ Icc (0 : ℝ) 1, (C.dl ξ' (γ t)).toReal ≤ δ := by
        intro t ht
        have := controlDistance_subcurve_le_param hγ le_rfl ht.1 ht.2
        rw [hγ0] at this
        exact ENNReal.toReal_le_of_le_ofReal hδ.le this
      have hpoleb : ∀ t ∈ Icc (0 : ℝ) 1,
          r / 2 ≤ (C.dl (γ t) η).toReal ∧ (C.dl (γ t) η).toReal ≤ 2 * r := by
        intro t ht
        have hγU := hεU (hmem t ht)
        have htri1 := C.dl_toReal_triangle hξ'U hγU hηU
        have htri2 := C.dl_toReal_triangle hγU hξ'U hηU
        have hs := hsub t ht
        have hsy : (C.dl (γ t) ξ').toReal = (C.dl ξ' (γ t)).toReal := by rw [C.dl_symm]
        rw [hsy] at htri2
        constructor <;> linarith
      have hbound := hB₁ η (self_subset_cthickening _ hη) δ r hδ (by linarith) γ hγ hmem hpoleb
      rw [hγ0, hγ1] at hbound
      rw [abs_sub_comm]
      refine hbound.trans ?_
      have h2 : δ * r ^ (d - 1) ≤ 2 * (h * r ^ (d - 1)) := by nlinarith
      calc B₁ * (δ * r ^ (d - 1)) ≤ B₁ * (2 * (h * r ^ (d - 1))) :=
            mul_le_mul_of_nonneg_left h2 hB₁0
        _ ≤ _ := by nlinarith [mul_nonneg hAc hhr]
    · -- endpoint size bounds
      have hrc : r ≤ c₂ * h := by
        by_cases h4 : 4 * h < r
        · have hr1 : r₁ ≤ 2 * h := by
            by_contra hcon
            exact hcase ⟨h4, not_le.mp hcon⟩
          have hrD : r ≤ D := by
            have h1 := C.dl_toReal_le hηU hξ'U
            have h2 : kgauge C.G (C.Θ η ξ') ≤ max R₀ 1 := (hR₀ η hη ξ' hξ').trans (le_max_left _ _)
            have h3 : r = (C.dl η ξ').toReal := by rw [hr, C.dl_symm ξ' η]
            rw [h3]
            exact h1.trans (mul_le_mul_of_nonneg_left h2 C.gaugeConst_pos.le)
          have h5 : D ≤ 2 * D / r₁ * h := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hr₁]
            nlinarith
          exact hrD.trans (h5.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hh0))
        · exact (not_lt.mp h4).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hh0)
      have hxlo : r - h ≤ (C.dl ξ η).toReal := by
        have := C.dl_toReal_triangle hξ'U hξU hηU
        linarith
      have hxhi : (C.dl ξ η).toReal ≤ r + h := by
        have := C.dl_toReal_triangle hξU hξ'U hηU
        linarith
      have hξη : ξ ≠ η := by
        intro he
        have : (C.dl ξ η).toReal = 0 := by
          rw [he, (C.dl_eq_zero_iff hηU hηU).mpr rfl, ENNReal.toReal_zero]
        linarith
      have hξ'η : ξ' ≠ η := by
        intro he
        have : r = 0 := by rw [hr, he, (C.dl_eq_zero_iff hηU hηU).mpr rfl, ENNReal.toReal_zero]
        linarith
      have hxpos : 0 < (C.dl ξ η).toReal := by linarith
      have hxd : (C.dl ξ η).toReal ^ d ≤ 2 ^ d.natAbs * r ^ d :=
        kzpow_le_const_mul (by norm_num : (1 : ℝ) ≤ 2) hxpos hr0 (by linarith) (by linarith) d
      have hA1 := hA ξ' hξ' η hη hξ'η
      have hA2 := hA ξ hξ η hη hξη
      have hrd' : r ^ d = r ^ (d - 1) * r := by
        rw [← zpow_add_one₀ hr0.ne']
        congr 1
        ring
      have hbig : |Ψ ξ' η (C.Θ η ξ') - Ψ ξ η (C.Θ η ξ)| ≤ A * (1 + 2 ^ d.natAbs) * r ^ d := by
        refine (abs_sub _ _).trans ?_
        have := mul_le_mul_of_nonneg_left hxd hA0
        nlinarith
      refine hbig.trans ?_
      rw [hrd']
      have h6 : A * (1 + 2 ^ d.natAbs) * (r ^ (d - 1) * r) ≤
          A * (1 + 2 ^ d.natAbs) * (r ^ (d - 1) * (c₂ * h)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrc hrd.le) (by positivity)
      refine h6.trans ?_
      nlinarith [mul_nonneg hB₁0 hhr, mul_nonneg hAc hhr]

end LiftedChart
end RothschildStein.P1

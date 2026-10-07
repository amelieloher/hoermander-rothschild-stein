-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimates

/-!
# Lipschitz factors and products of kernel bounds

The singular split `K = K₀ + K₁` of BB Prop 11.33 (pp. 572–576) is estimated by multiplying a
kernel with the lifted homogeneous kernel estimates by a *smooth bounded factor*: the density factor
`1/(1 + ω₋(ξ, Θ(η, ξ)))` for `K₀`, the diagonal factor `ω₋/(1 + ω₋)` (which vanishes on the
diagonal) for the first part of `K₁`, and the coordinate differences `(η - ξ)_l` (the parameter
mean value) for the second part of `K₁`. This file proves the abstract algebra:

* `HasKernelBounds`: the size and difference estimates of exponent `ℓ` on a compact
  `L ⊆ U` (`ℓ = 0` is singular exponent 1, `ℓ = 1` is fractional exponents `(1, 1)`);
* a function that is `C¹` on `U × U` is Lipschitz for the lifted control distance `d̃` in either
  variable, uniformly on compact subsets, by integrating the lifted derivatives along a controlled
  curve (as in the path margin of the kernel estimates); in particular it is `O(d̃)` where it vanishes on the diagonal;
* the product of a kernel with bounds of exponent `ℓ` and a `d̃`-Lipschitz factor of size
  `O(d̃^e)`, `e ∈ {0, 1}`, has bounds of exponent `ℓ + e` (BB pp. 573–575: "product differences
  add `O(h r^{-Q})` ... absorbed on the fixed patch").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
open scoped BigOperators ENNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Lifted kernel estimates of exponent `ℓ` on `L`: size
`|κ(ξ, η)| ≤ A d̃(ξ, η)^(ℓ - Q)` and the difference bound
`|κ(ξ', η) - κ(ξ, η)| + |κ(η, ξ') - κ(η, ξ)| ≤ S d̃(ξ, ξ') / d̃(ξ', η)^(Q + 1 - ℓ)` when
`d̃(ξ', η) > 2 d̃(ξ, ξ')`. This is the conclusion of the kernel estimates (`exists_kernel_estimates_cutoff`);
`ℓ = 0` is singular exponent 1 and `ℓ = 1` is fractional exponents `(1, 1)` (BB p. 299,
Def 7.10 with `ν = ℓ`, `β = 1`; the denominator `d̃^(Q+1-ℓ)` is the erratum-corrected one). -/
def HasKernelBounds (L : Set (Fin (n + m) → ℝ)) (ℓ : ℕ)
    (κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) : Prop :=
  ∃ A S : ℝ, 0 ≤ A ∧ 0 ≤ S ∧
    (∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η →
      |κ ξ η| ≤ A * (C.dl ξ η).toReal ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ))) ∧
    (∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L, 2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
      |κ ξ' η - κ ξ η| + |κ η ξ' - κ η ξ| ≤
        S * (C.dl ξ ξ').toReal /
          (C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)))

variable {C}
variable {L : Set (Fin (n + m) → ℝ)} {ℓ : ℕ}
  {κ κ₁ κ₂ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- The zero kernel has kernel bounds of every exponent. -/
theorem HasKernelBounds.zero : C.HasKernelBounds L ℓ (fun _ _ => 0) :=
  ⟨0, 0, le_rfl, le_rfl, fun _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => by simp⟩

/-- Kernel bounds of the same exponent are stable under pointwise equality on `L × L`. -/
theorem HasKernelBounds.congr (h : C.HasKernelBounds L ℓ κ₁)
    (he : ∀ ξ ∈ L, ∀ η ∈ L, κ₁ ξ η = κ₂ ξ η) : C.HasKernelBounds L ℓ κ₂ := by
  obtain ⟨A, S, hA, hS, hsz, hdf⟩ := h
  refine ⟨A, S, hA, hS, fun ξ hξ η hη hne => ?_, fun ξ hξ ξ' hξ' η hη hsep => ?_⟩
  · rw [← he ξ hξ η hη]
    exact hsz ξ hξ η hη hne
  · rw [← he ξ' hξ' η hη, ← he ξ hξ η hη, ← he η hη ξ' hξ', ← he η hη ξ hξ]
    exact hdf ξ hξ ξ' hξ' η hη hsep

/-- Kernel bounds of the same exponent add (the constants add). -/
theorem HasKernelBounds.add (h₁ : C.HasKernelBounds L ℓ κ₁) (h₂ : C.HasKernelBounds L ℓ κ₂) :
    C.HasKernelBounds L ℓ (fun ξ η => κ₁ ξ η + κ₂ ξ η) := by
  obtain ⟨A₁, S₁, hA₁, hS₁, hsz₁, hdf₁⟩ := h₁
  obtain ⟨A₂, S₂, hA₂, hS₂, hsz₂, hdf₂⟩ := h₂
  refine ⟨A₁ + A₂, S₁ + S₂, add_nonneg hA₁ hA₂, add_nonneg hS₁ hS₂, ?_, ?_⟩
  · intro ξ hξ η hη hne
    calc |κ₁ ξ η + κ₂ ξ η| ≤ |κ₁ ξ η| + |κ₂ ξ η| := abs_add_le _ _
      _ ≤ A₁ * (C.dl ξ η).toReal ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ)) +
          A₂ * (C.dl ξ η).toReal ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ)) :=
        add_le_add (hsz₁ ξ hξ η hη hne) (hsz₂ ξ hξ η hη hne)
      _ = _ := by ring
  · intro ξ hξ ξ' hξ' η hη hsep
    have h1 := hdf₁ ξ hξ ξ' hξ' η hη hsep
    have h2 := hdf₂ ξ hξ ξ' hξ' η hη hsep
    have e1 : |κ₁ ξ' η + κ₂ ξ' η - (κ₁ ξ η + κ₂ ξ η)| ≤
        |κ₁ ξ' η - κ₁ ξ η| + |κ₂ ξ' η - κ₂ ξ η| := by
      have : κ₁ ξ' η + κ₂ ξ' η - (κ₁ ξ η + κ₂ ξ η) =
          (κ₁ ξ' η - κ₁ ξ η) + (κ₂ ξ' η - κ₂ ξ η) := by ring
      rw [this]
      exact abs_add_le _ _
    have e2 : |κ₁ η ξ' + κ₂ η ξ' - (κ₁ η ξ + κ₂ η ξ)| ≤
        |κ₁ η ξ' - κ₁ η ξ| + |κ₂ η ξ' - κ₂ η ξ| := by
      have : κ₁ η ξ' + κ₂ η ξ' - (κ₁ η ξ + κ₂ η ξ) =
          (κ₁ η ξ' - κ₁ η ξ) + (κ₂ η ξ' - κ₂ η ξ) := by ring
      rw [this]
      exact abs_add_le _ _
    calc _ ≤ (|κ₁ ξ' η - κ₁ ξ η| + |κ₁ η ξ' - κ₁ η ξ|) +
          (|κ₂ ξ' η - κ₂ ξ η| + |κ₂ η ξ' - κ₂ η ξ|) := by linarith
      _ ≤ S₁ * (C.dl ξ ξ').toReal /
            (C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)) +
          S₂ * (C.dl ξ ξ').toReal /
            (C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)) :=
        add_le_add h1 h2
      _ = _ := by ring

/-- Finite sums of kernels with bounds of the same exponent have bounds of that
exponent. -/
theorem HasKernelBounds.finset_sum {ι : Type*} (S : Finset ι) {κ : ι → (Fin (n + m) → ℝ) →
    (Fin (n + m) → ℝ) → ℝ} (h : ∀ i ∈ S, C.HasKernelBounds L ℓ (κ i)) :
    C.HasKernelBounds L ℓ (fun ξ η => ∑ i ∈ S, κ i ξ η) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (HasKernelBounds.zero (C := C) (L := L) (ℓ := ℓ))
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    simpa only [Finset.sum_insert ha] using this

section Distance

variable (hL : IsCompact L) (hLU : L ⊆ C.U)
include hL hLU

/-- The lifted control distance is bounded on a compact subset of `U` (lifted-chart field `gauge_comparison`). -/
theorem exists_dl_bound : ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ ξ ∈ L, ∀ η ∈ L, (C.dl ξ η).toReal ≤ D₀ := by
  obtain ⟨R₀, hR₀⟩ := C.exists_gauge_bound hL hLU
  refine ⟨C.gaugeConst * max R₀ 1, mul_pos C.gaugeConst_pos (lt_of_lt_of_le one_pos
    (le_max_right _ _)), fun ξ hξ η hη => ?_⟩
  exact (C.dl_toReal_le (hLU hξ) (hLU hη)).trans
    (mul_le_mul_of_nonneg_left ((hR₀ ξ hξ η hη).trans (le_max_left _ _)) C.gaugeConst_pos.le)

end Distance

/-- Distinct points: positive lifted distance forces `a ≠ b`. -/
theorem ne_of_dl_toReal_pos {a b : Fin (n + m) → ℝ} (ha : a ∈ C.U)
    (h : 0 < (C.dl a b).toReal) : a ≠ b := by
  rintro rfl
  rw [(C.dl_eq_zero_iff ha ha).mpr rfl, ENNReal.toReal_zero] at h
  exact lt_irrefl _ h

section Lipschitz

variable {G : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ}
variable (hG : ContDiffOn ℝ 1 G (C.U ×ˢ C.U)) (hL : IsCompact L) (hLU : L ⊆ C.U)
include hG hL hLU

/-- A function `C¹` on `U × U` is Lipschitz for the lifted control distance in the first
variable, uniformly in the second variable, on a compact `L ⊆ U`: integrate the derivative bounds
along `X̃_i` over a controlled curve of parameter `< 2 d̃(ξ, ξ')` (the path margin of the kernel estimates), and use the
sup bound for distant pairs. -/
theorem exists_lipschitz_first : ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L,
    |G (ξ', η) - G (ξ, η)| ≤ M * (C.dl ξ ξ').toReal := by
  obtain ⟨ε, hε, hεU, r₁, hr₁, hmargin⟩ := C.exists_path_margin hL hLU
  have hL₁ : IsCompact (cthickening ε L) := hL.cthickening
  have hUU : IsOpen (C.U ×ˢ C.U) := C.isOpen_U.prod C.isOpen_U
  obtain ⟨S, hS⟩ := (hL.prod hL).exists_bound_of_continuousOn
    (hG.continuousOn.mono (Set.prod_mono hLU hLU))
  have hXc : ∀ i, ContinuousOn (C.Xl i) C.U :=
    fun i => ((C.lift_smooth i).continuousOn).mono C.U_subset_O
  have hDc : ContinuousOn (fderiv ℝ G) (C.U ×ˢ C.U) :=
    hG.continuousOn_fderiv_of_isOpen hUU le_rfl
  have hB : ∀ i, ∃ B : ℝ, ∀ z ∈ cthickening ε L, ∀ η ∈ L,
      |fderiv ℝ G (z, η) (C.Xl i z, 0)| ≤ B := by
    intro i
    have hsub : cthickening ε L ×ˢ L ⊆ C.U ×ˢ C.U := Set.prod_mono hεU hLU
    have hcont : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        fderiv ℝ G (p.1, p.2) (C.Xl i p.1, 0)) (cthickening ε L ×ˢ L) := by
      refine ContinuousOn.clm_apply (hDc.mono hsub) ?_
      exact (((hXc i).mono (hεU)).comp continuousOn_fst
        (fun p hp => hp.1)).prodMk continuousOn_const
    obtain ⟨B, hB⟩ := (hL₁.prod hL).exists_bound_of_continuousOn hcont
    exact ⟨B, fun z hz η hη => by simpa using hB (z, η) ⟨hz, hη⟩⟩
  choose B hB using hB
  set M₁ : ℝ := ∑ i, |B i| with hM₁
  have hM₁0 : 0 ≤ M₁ := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  set t₀ : ℝ := min r₁ 1 with ht₀
  have ht₀pos : 0 < t₀ := lt_min hr₁ one_pos
  refine ⟨max (2 * M₁) (4 * |S| / t₀), le_max_of_le_left (by positivity), ?_⟩
  intro ξ hξ ξ' hξ' η hη
  have hξU := hLU hξ
  have hξ'U := hLU hξ'
  have hηU := hLU hη
  set h : ℝ := (C.dl ξ ξ').toReal with hh
  have hh0 : 0 ≤ h := ENNReal.toReal_nonneg
  rcases hh0.eq_or_lt with hz | hpos
  · have hdl : C.dl ξ ξ' = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hz.symm with h0 | h0
      · exact h0
      · exact absurd h0 (C.dl_ne_top hξU hξ'U)
    have hee : ξ' = ξ := (C.dl_eq_zero_iff hξU hξ'U).mp hdl
    rw [hee, sub_self, abs_zero, ← hz, mul_zero]
  · by_cases hsmall : h < t₀ / 2
    · -- near pairs: path argument
      have hlt : C.dl ξ ξ' < ENNReal.ofReal (2 * h) := by
        have : C.dl ξ ξ' = ENNReal.ofReal h := by
          rw [hh, ENNReal.ofReal_toReal (C.dl_ne_top hξU hξ'U)]
        rw [this]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
      obtain ⟨δ, hδ, hδ2h, γ, hγ, hγ0, hγ1⟩ :=
        RothschildStein.G1.exists_controlledCurve_of_controlDistance_lt hlt
      have hδr : δ < r₁ := by
        have : t₀ ≤ r₁ := min_le_left _ _
        linarith
      have hδ1 : δ ≤ 1 := by
        have : t₀ ≤ 1 := min_le_right _ _
        linarith
      have hmem := hmargin ξ hξ δ hδr γ hγ hγ0
      have hΩ' : isControlledCurve C.U w C.Xl δ γ :=
        isControlledCurve_restrict hγ (fun t ht => hεU (hmem t ht))
      have hf : ContDiffOn ℝ 1 (fun ζ => G (ζ, η)) C.U :=
        hG.comp (contDiffOn_id.prodMk contDiffOn_const) (fun ζ hζ => ⟨hζ, hηU⟩)
      have hderiv : ∀ z ∈ C.U, ∀ v : Fin (n + m) → ℝ,
          fderiv ℝ (fun ζ => G (ζ, η)) z v = fderiv ℝ G (z, η) (v, 0) := by
        intro z hz v
        have hGd : DifferentiableAt ℝ G (z, η) :=
          (hG.differentiableOn one_ne_zero).differentiableAt (hUU.mem_nhds ⟨hz, hηU⟩)
        have hinj : HasFDerivAt (fun ζ : Fin (n + m) → ℝ => (ζ, η))
            ((ContinuousLinearMap.id ℝ (Fin (n + m) → ℝ)).prod
              (0 : (Fin (n + m) → ℝ) →L[ℝ] (Fin (n + m) → ℝ))) z :=
          (hasFDerivAt_id z).prodMk (hasFDerivAt_const η z)
        have hcomp := hGd.hasFDerivAt.comp z hinj
        have hcomp' : HasFDerivAt (fun ζ : Fin (n + m) → ℝ => G (ζ, η))
            ((fderiv ℝ G (z, η)).comp ((ContinuousLinearMap.id ℝ (Fin (n + m) → ℝ)).prod
              (0 : (Fin (n + m) → ℝ) →L[ℝ] (Fin (n + m) → ℝ)))) z := hcomp
        rw [hcomp'.fderiv]
        simp
      have hvar := RothschildStein.G1.controlledCurve_variation_le C.isOpen_U hf hΩ'
        (C := δ * M₁) (fun t ht => by
          have hz := hεU (hmem t ht)
          rw [hM₁, Finset.mul_sum]
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [hderiv _ hz]
          have hpw : δ ^ (w i : ℕ) ≤ δ :=
            pow_le_of_le_one hδ.le hδ1 (by have := (w i).pos; omega)
          calc δ ^ (w i : ℕ) * |fderiv ℝ G (γ t, η) (C.Xl i (γ t), 0)|
              ≤ δ * |B i| := by
                refine mul_le_mul hpw ?_ (abs_nonneg _) hδ.le
                exact (hB i (γ t) (hmem t ht) η hη).trans (le_abs_self _)
            _ = δ * |B i| := rfl)
      rw [hγ0, hγ1] at hvar
      refine hvar.trans ?_
      have : δ * M₁ ≤ 2 * M₁ * h := by nlinarith
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hh0)
    · -- distant pairs: sup bounds
      have hfar : t₀ / 2 ≤ h := not_lt.mp hsmall
      have h1 : ‖G (ξ', η)‖ ≤ S := hS (ξ', η) ⟨hξ', hη⟩
      have h2 : ‖G (ξ, η)‖ ≤ S := hS (ξ, η) ⟨hξ, hη⟩
      rw [Real.norm_eq_abs] at h1 h2
      have h3 : |G (ξ', η) - G (ξ, η)| ≤ 2 * |S| := by
        have := abs_sub (G (ξ', η)) (G (ξ, η))
        have := le_abs_self S
        linarith
      refine h3.trans ?_
      have h4 : 2 * |S| ≤ 4 * |S| / t₀ * h := by
        rw [div_mul_eq_mul_div, le_div_iff₀ ht₀pos]
        nlinarith [abs_nonneg S]
      exact h4.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hh0)

/-- The same Lipschitz bound in the second variable, uniformly in the first. -/
theorem exists_lipschitz_second : ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L,
    |G (η, ξ') - G (η, ξ)| ≤ M * (C.dl ξ ξ').toReal := by
  have hG' : ContDiffOn ℝ 1 (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => G (p.2, p.1))
      (C.U ×ˢ C.U) :=
    hG.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => ⟨hp.2, hp.1⟩)
  exact C.exists_lipschitz_first hG' hL hLU

/-- Both Lipschitz bounds with one constant. -/
theorem exists_lipschitz : ∃ M : ℝ, 0 ≤ M ∧
    (∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L, |G (ξ', η) - G (ξ, η)| ≤ M * (C.dl ξ ξ').toReal) ∧
    (∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L, |G (η, ξ') - G (η, ξ)| ≤ M * (C.dl ξ ξ').toReal) := by
  obtain ⟨M₁, h₁0, h₁⟩ := C.exists_lipschitz_first hG hL hLU
  obtain ⟨M₂, h₂0, h₂⟩ := C.exists_lipschitz_second hG hL hLU
  refine ⟨max M₁ M₂, le_max_of_le_left h₁0, fun ξ hξ ξ' hξ' η hη => ?_,
    fun ξ hξ ξ' hξ' η hη => ?_⟩
  · exact (h₁ ξ hξ ξ' hξ' η hη).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      ENNReal.toReal_nonneg)
  · exact (h₂ ξ hξ ξ' hξ' η hη).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      ENNReal.toReal_nonneg)

/-- A function `C¹` on `U × U` is bounded on `L × L`. -/
theorem exists_bound_prod : ∃ S : ℝ, 0 ≤ S ∧ ∀ ξ ∈ L, ∀ η ∈ L, |G (ξ, η)| ≤ S := by
  obtain ⟨S, hS⟩ := (hL.prod hL).exists_bound_of_continuousOn
    (hG.continuousOn.mono (Set.prod_mono hLU hLU))
  refine ⟨|S|, abs_nonneg _, fun ξ hξ η hη => ?_⟩
  have := hS (ξ, η) ⟨hξ, hη⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_abs_self _)

/-- A function `C¹` on `U × U` that vanishes on the diagonal of `L` is `O(d̃)`:
`|G(ξ, η)| ≤ M d̃(ξ, η)` (BB p. 574: "`f` vanishes on the diagonal, so `|f| ≤ C ρ`"). -/
theorem exists_size_of_diag_zero (hdiag : ∀ ξ ∈ L, G (ξ, ξ) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ L, ∀ η ∈ L, |G (ξ, η)| ≤ M * (C.dl ξ η).toReal := by
  obtain ⟨M, hM0, hM⟩ := C.exists_lipschitz_second hG hL hLU
  refine ⟨M, hM0, fun ξ hξ η hη => ?_⟩
  have := hM ξ hξ η hη ξ hξ
  rwa [hdiag ξ hξ, sub_zero] at this

end Lipschitz

section Product

variable (hL : IsCompact L) (hLU : L ⊆ C.U)
include hL hLU

/-- **Product of a kernel with bounds and a Lipschitz factor** (BB pp. 573–575). If `κ`
has kernel bounds of exponent `ℓ` and `g` is `O(d̃^e)` (`e ∈ {0, 1}`) and `d̃`-Lipschitz in each
variable, then `g κ` has kernel bounds of exponent `ℓ + e`: size `Gs · A · d̃^(ℓ + e - Q)`, and the
difference splits as `g(ξ', η)(κ(ξ', η) - κ(ξ, η)) + κ(ξ, η)(g(ξ', η) - g(ξ, η))`, where the second
term is `O(h r^(ℓ - Q)) = O(h r^(ℓ + e - Q - 1))` on the bounded patch. -/
theorem HasKernelBounds.mul {e : ℕ} (he : e ≤ 1) {g : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : C.HasKernelBounds L ℓ κ) {Gs M : ℝ} (hGs : 0 ≤ Gs) (hM : 0 ≤ M)
    (hsize : ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η → |g ξ η| ≤ Gs * (C.dl ξ η).toReal ^ e)
    (hlip₁ : ∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L, |g ξ' η - g ξ η| ≤ M * (C.dl ξ ξ').toReal)
    (hlip₂ : ∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L, |g η ξ' - g η ξ| ≤ M * (C.dl ξ ξ').toReal) :
    C.HasKernelBounds L (ℓ + e) (fun ξ η => g ξ η * κ ξ η) := by
  obtain ⟨A, S, hA, hS, hsz, hdf⟩ := hκ
  obtain ⟨D₀, hD₀, hD⟩ := C.exists_dl_bound hL hLU
  set Q : ℤ := (C.G.homogeneousDimension : ℤ) with hQ
  set D₁ : ℝ := max 1 D₀ with hD₁
  have hD₁1 : 1 ≤ D₁ := le_max_left _ _
  set c : ℝ := 2 ^ ((ℓ : ℤ) - Q).natAbs with hc
  have hc1 : 1 ≤ c := one_le_pow₀ (by norm_num)
  refine ⟨Gs * A, Gs * S + 2 * (A * c * M * D₁), by positivity, by positivity, ?_, ?_⟩
  · intro ξ hξ η hη hne
    have hd : 0 < (C.dl ξ η).toReal := C.dl_toReal_pos (hLU hξ) (hLU hη) hne.symm
    set d : ℝ := (C.dl ξ η).toReal with hdd
    have hsplit : d ^ (((ℓ + e : ℕ) : ℤ) - Q) = d ^ (e : ℤ) * d ^ ((ℓ : ℤ) - Q) := by
      rw [← zpow_add₀ hd.ne']
      congr 1
      push_cast
      ring
    calc |g ξ η * κ ξ η| = |g ξ η| * |κ ξ η| := abs_mul _ _
      _ ≤ (Gs * d ^ e) * (A * d ^ ((ℓ : ℤ) - Q)) :=
          mul_le_mul (hsize ξ hξ η hη hne) (hsz ξ hξ η hη hne) (abs_nonneg _) (by positivity)
      _ = Gs * A * d ^ (((ℓ + e : ℕ) : ℤ) - Q) := by
          rw [hsplit, zpow_natCast]
          ring
  · intro ξ hξ ξ' hξ' η hη hsep
    have hξU := hLU hξ
    have hξ'U := hLU hξ'
    have hηU := hLU hη
    set h : ℝ := (C.dl ξ ξ').toReal with hh
    set r : ℝ := (C.dl ξ' η).toReal with hr
    have hh0 : 0 ≤ h := ENNReal.toReal_nonneg
    have hr0 : 0 < r := by linarith
    have hξ'η : ξ' ≠ η := C.ne_of_dl_toReal_pos hξ'U hr0
    have hk := hdf ξ hξ ξ' hξ' η hη hsep
    -- positions of `d̃(ξ, η)`
    have hxlo : r - h ≤ (C.dl ξ η).toReal := by
      have := C.dl_toReal_triangle hξ'U hξU hηU
      have hs : (C.dl ξ' ξ).toReal = h := by rw [hh, C.dl_symm ξ' ξ]
      linarith
    have hxhi : (C.dl ξ η).toReal ≤ r + h := by
      have := C.dl_toReal_triangle hξU hξ'U hηU
      linarith
    have hxpos : 0 < (C.dl ξ η).toReal := by linarith
    have hξη : ξ ≠ η := C.ne_of_dl_toReal_pos hξU hxpos
    have hηξ : η ≠ ξ := hξη.symm
    have hdsy : (C.dl η ξ).toReal = (C.dl ξ η).toReal := by rw [C.dl_symm η ξ]
    have hdsy' : (C.dl η ξ').toReal = r := by rw [hr, C.dl_symm η ξ']
    -- the sizes of the factor at the two points
    have hg1 : |g ξ' η| ≤ Gs * r ^ e := hsize ξ' hξ' η hη hξ'η
    have hg2 : |g η ξ'| ≤ Gs * r ^ e := by
      have := hsize η hη ξ' hξ' hξ'η.symm
      rwa [hdsy'] at this
    -- the sizes of the kernel at `(ξ, η)`
    have hκ1 := hsz ξ hξ η hη hξη
    have hκ2 := hsz η hη ξ hξ hηξ
    rw [hdsy] at hκ2
    have hxr : (C.dl ξ η).toReal ^ ((ℓ : ℤ) - Q) ≤ c * r ^ ((ℓ : ℤ) - Q) :=
      kzpow_le_const_mul (by norm_num : (1 : ℝ) ≤ 2) hxpos hr0 (by linarith) (by linarith) _
    -- exponent bookkeeping
    set P : ℝ := r ^ (Q + 1 - ((ℓ + e : ℕ) : ℤ)) with hP
    have hPpos : 0 < P := zpow_pos hr0 _
    have hrp : r ^ ((ℓ : ℤ) - Q) ≤ D₁ / P := by
      rw [le_div_iff₀ hPpos, hP, ← zpow_add₀ hr0.ne']
      have hexp : ((ℓ : ℤ) - Q) + (Q + 1 - ((ℓ + e : ℕ) : ℤ)) = 1 - (e : ℤ) := by
        push_cast
        ring
      rw [hexp]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
      · simp only [Nat.cast_zero, sub_zero, zpow_one]
        exact (hD ξ' hξ' η hη).trans (le_max_right _ _)
      · simp only [Nat.cast_one, sub_self, zpow_zero]
        exact hD₁1
    have hrk : r ^ e * (1 / r ^ (Q + 1 - (ℓ : ℤ))) = 1 / P := by
      rw [hP]
      have : r ^ (Q + 1 - (ℓ : ℤ)) = r ^ (Q + 1 - ((ℓ + e : ℕ) : ℤ)) * r ^ e := by
        rw [← zpow_natCast r e, ← zpow_add₀ hr0.ne']
        congr 1
        push_cast
        ring
      rw [this]
      field_simp
    -- the two decompositions
    have d1 : |g ξ' η * κ ξ' η - g ξ η * κ ξ η| ≤
        |g ξ' η| * |κ ξ' η - κ ξ η| + |κ ξ η| * |g ξ' η - g ξ η| := by
      have : g ξ' η * κ ξ' η - g ξ η * κ ξ η =
          g ξ' η * (κ ξ' η - κ ξ η) + κ ξ η * (g ξ' η - g ξ η) := by ring
      rw [this]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul]
    have d2 : |g η ξ' * κ η ξ' - g η ξ * κ η ξ| ≤
        |g η ξ'| * |κ η ξ' - κ η ξ| + |κ η ξ| * |g η ξ' - g η ξ| := by
      have : g η ξ' * κ η ξ' - g η ξ * κ η ξ =
          g η ξ' * (κ η ξ' - κ η ξ) + κ η ξ * (g η ξ' - g η ξ) := by ring
      rw [this]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul]
    have hGr : 0 ≤ Gs * r ^ e := by positivity
    have t1 : |g ξ' η| * |κ ξ' η - κ ξ η| + |g η ξ'| * |κ η ξ' - κ η ξ| ≤
        Gs * r ^ e * (|κ ξ' η - κ ξ η| + |κ η ξ' - κ η ξ|) := by
      have a1 := mul_le_mul_of_nonneg_right hg1 (abs_nonneg (κ ξ' η - κ ξ η))
      have a2 := mul_le_mul_of_nonneg_right hg2 (abs_nonneg (κ η ξ' - κ η ξ))
      nlinarith
    have t2 : Gs * r ^ e * (|κ ξ' η - κ ξ η| + |κ η ξ' - κ η ξ|) ≤
        Gs * S * h / P := by
      calc Gs * r ^ e * (|κ ξ' η - κ ξ η| + |κ η ξ' - κ η ξ|)
          ≤ Gs * r ^ e * (S * h / r ^ (Q + 1 - (ℓ : ℤ))) := mul_le_mul_of_nonneg_left hk hGr
        _ = Gs * S * h * (r ^ e * (1 / r ^ (Q + 1 - (ℓ : ℤ)))) := by ring
        _ = Gs * S * h / P := by rw [hrk]; ring
    have hxA : |κ ξ η| ≤ A * (c * r ^ ((ℓ : ℤ) - Q)) :=
      hκ1.trans (mul_le_mul_of_nonneg_left hxr hA)
    have hxA' : |κ η ξ| ≤ A * (c * r ^ ((ℓ : ℤ) - Q)) :=
      hκ2.trans (mul_le_mul_of_nonneg_left hxr hA)
    have hAc : 0 ≤ A * (c * r ^ ((ℓ : ℤ) - Q)) := by positivity
    have l1 := mul_le_mul hxA (hlip₁ ξ hξ ξ' hξ' η hη) (abs_nonneg _) hAc
    have l2 := mul_le_mul hxA' (hlip₂ ξ hξ ξ' hξ' η hη) (abs_nonneg _) hAc
    have t3 : A * (c * r ^ ((ℓ : ℤ) - Q)) * (M * h) ≤ A * c * M * D₁ * h / P := by
      have h1 : A * (c * r ^ ((ℓ : ℤ) - Q)) * (M * h) =
          A * c * M * h * r ^ ((ℓ : ℤ) - Q) := by ring
      rw [h1]
      calc A * c * M * h * r ^ ((ℓ : ℤ) - Q) ≤ A * c * M * h * (D₁ / P) :=
            mul_le_mul_of_nonneg_left hrp (by positivity)
        _ = A * c * M * D₁ * h / P := by ring
    have hmain : |g ξ' η * κ ξ' η - g ξ η * κ ξ η| + |g η ξ' * κ η ξ' - g η ξ * κ η ξ| ≤
        (Gs * S + 2 * (A * c * M * D₁)) * h / P := by
      have e1 : (Gs * S + 2 * (A * c * M * D₁)) * h / P =
          Gs * S * h / P + A * c * M * D₁ * h / P + A * c * M * D₁ * h / P := by ring
      rw [e1]
      linarith
    exact hmain

end Product

end LiftedChart
end RothschildStein.P1

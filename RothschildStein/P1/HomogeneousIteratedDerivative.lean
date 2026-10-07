-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.IteratedLinearPullback
public import RothschildStein.P1.DilationDerivativeNorm

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.P1

/-- Every retained ordinary derivative of a smooth
punctured homogeneous kernel has the corresponding weighted decay. The
loss is bounded by the number of derivatives times the largest coordinate
weight; constants may depend on the derivative order. -/
theorem exists_homogeneous_iteratedFDeriv_bound {N : ℕ} (G : HomogeneousGroup N)
    (W : ℕ) (hW : ∀ i, G.weight i ≤ W)
    (g : (Fin N → ℝ) → ℝ) (d : ℤ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      g (G.dilate r u) = r ^ d * g u) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin N → ℝ, u ≠ 0 → kgauge G u ≤ 1 →
      ‖iteratedFDeriv ℝ j g u‖ ≤ C * kgauge G u ^ (d - ((j * W : ℕ) : ℤ)) := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ j g) {(0 : Fin N → ℝ)}ᶜ :=
    ContinuousOn.continuousOn_iteratedFDeriv hg isOpen_compl_singleton (by simp)
  have hunit : IsCompact {u : Fin N → ℝ | kgauge G u = 1} := by
    simpa only [kgauge] using G2.isCompact_max_unit G
  have hsub : {u : Fin N → ℝ | kgauge G u = 1} ⊆ {(0 : Fin N → ℝ)}ᶜ := by
    intro u hu
    change u ≠ 0
    intro he
    have hzero := (kgauge_eq_zero_iff G u).mpr he
    change kgauge G u = 1 at hu
    linarith
  obtain ⟨C, hc⟩ := hunit.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro u hu hρle
  let ρ := kgauge G u
  have hρ : 0 < ρ := kgauge_pos G hu
  let L := kdilateCLM G ρ⁻¹
  have hv : L u ≠ 0 := by
    rw [kdilateCLM_apply]
    exact kdilate_ne_zero G (inv_pos.mpr hρ) hu
  have hvunit : kgauge G (L u) = 1 := by
    rw [kdilateCLM_apply]
    exact G2.gauge_normalize (G2.isHomogeneousGauge_max G) hu
  have hnorm : ‖L‖ ≤ ρ⁻¹ ^ W :=
    norm_kdilateCLM_le_pow G W hW ((one_le_inv₀ hρ).mpr hρle)
  have hchain := iteratedFDeriv_comp_linear_of_contDiffOn L g {(0 : Fin N → ℝ)}ᶜ
    isOpen_compl_singleton hg j u hv
  have heq : EqOn g (fun x => ρ ^ d * g (L x)) {(0 : Fin N → ℝ)}ᶜ := by
    intro x hx
    have hLx : L x ≠ 0 := by
      rw [kdilateCLM_apply]
      exact kdilate_ne_zero G (inv_pos.mpr hρ) hx
    have he := hhom ρ hρ (L x) hLx
    rw [kdilateCLM_apply, kdilate_dilate, mul_inv_cancel₀ hρ.ne', kdilate_one] at he
    exact he
  have hloc : ContDiffAt ℝ j (g ∘ L) u :=
    ((hg.contDiffAt (isOpen_compl_singleton.mem_nhds hv)).comp u L.contDiff.contDiffAt).of_le (by simp)
  have hder := iteratedFDerivWithin_congr (𝕜 := ℝ) heq hu j
  rw [iteratedFDerivWithin_of_isOpen j isOpen_compl_singleton hu,
    iteratedFDerivWithin_of_isOpen j isOpen_compl_singleton hu] at hder
  have hder' : iteratedFDeriv ℝ j g u = ρ ^ d • iteratedFDeriv ℝ j (g ∘ L) u := by
    rw [hder]
    exact iteratedFDeriv_const_smul_apply (a := (ρ ^ d : ℝ)) hloc
  rw [hder', norm_smul, Real.norm_eq_abs, abs_of_pos (zpow_pos hρ d), hchain]
  have hcomp : ‖(iteratedFDeriv ℝ j g (L u)).compContinuousLinearMap (fun _ => L)‖ ≤
      ‖iteratedFDeriv ℝ j g (L u)‖ * ‖L‖ ^ j := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ j g (L u)).norm_compContinuousLinearMap_le (fun _ => L)
  have hb : ‖iteratedFDeriv ℝ j g (L u)‖ ≤ |C| := (hc _ hvunit).trans (le_abs_self C)
  have hpow : (ρ⁻¹ ^ W) ^ j = ρ ^ (-((j * W : ℕ) : ℤ)) := by
    rw [← pow_mul, zpow_neg, zpow_natCast, inv_pow, Nat.mul_comm W j]
  calc
    _ ≤ ρ ^ d * (‖iteratedFDeriv ℝ j g (L u)‖ * ‖L‖ ^ j) :=
      mul_le_mul_of_nonneg_left hcomp (zpow_nonneg hρ.le _)
    _ ≤ ρ ^ d * (|C| * (ρ⁻¹ ^ W) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (zpow_nonneg hρ.le _)
      exact mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg L) hnorm j)
        (pow_nonneg (norm_nonneg L) _) (abs_nonneg C)
    _ = |C| * (ρ ^ d * ρ ^ (-((j * W : ℕ) : ℤ))) := by rw [hpow]; ring
    _ = |C| * ρ ^ (d - ((j * W : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hρ.ne', ← sub_eq_add_neg]

end RothschildStein.P1

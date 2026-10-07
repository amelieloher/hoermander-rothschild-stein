-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.PartialSpatialJets
public import Mathlib.Analysis.Calculus.VectorField

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual spatial bracket of parameter-dependent fields,
viewed jointly in parameter and spatial coordinates (BB pp. 441–443). -/
def spatialBracketFamily {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Z Y : P × E → E) : P × E → E :=
  fun p => VectorField.lieBracket ℝ (fun x => Z (p.1, x)) (fun x => Y (p.1, x)) p.2

/-- Actual spatial brackets preserve joint parameter/spatial
smoothness on the original open domain (BB Lemma 9.48, pp. 441–443). -/
theorem spatialBracketFamily_contDiffOn {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (P × E)} (hS : IsOpen S) {Z Y : P × E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z S) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spatialBracketFamily Z Y) S := by
  exact ((partial_spatial_fderiv_contDiffOn hS hY).clm_apply hZ).sub
    ((partial_spatial_fderiv_contDiffOn hS hZ).clm_apply hY)

/-- The binomial estimate for a full joint jet of a spatial
field derivative loses exactly one joint field jet (BB pp. 441–443). -/
theorem norm_joint_spatial_derivative_jet_le {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (P × E)} (hS : IsOpen S) {Z Y : P × E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z S) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y S)
    {p : P × E} (hp : p ∈ S) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ (fun x => Y (q.1, x)) q.2 (Z q)) p‖ ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ‖iteratedFDeriv ℝ (j + 1) Y p‖ * ‖iteratedFDeriv ℝ (n - j) Z p‖ := by
  have hh := norm_iteratedFDerivWithin_clm_apply (n := n)
    (partial_spatial_fderiv_contDiffOn hS hY) hZ hS.uniqueDiffOn hp (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hS hp] at hh
  apply hh.trans
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_partial_spatial_fderiv_jet_le hS hY hp j)
      (Nat.cast_nonneg _)) (norm_nonneg _)

/-- A full joint spatial-bracket jet has a bound bilinear in the
two finite field-jet bounds (BB Lemma 9.48, pp. 441–443). -/
theorem norm_spatialBracketFamily_jet_le {P E : Type*} {R n : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (P × E)} (hS : IsOpen S) {Z Y : P × E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z S) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y S)
    {p : P × E} (hp : p ∈ S) (hn : n + 1 ≤ R) {B F : ℝ}
    (hZjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j Z p‖ ≤ B)
    (hYjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j Y p‖ ≤ F) :
    ‖iteratedFDeriv ℝ n (spatialBracketFamily Z Y) p‖ ≤ 2 ^ (n + 1) * B * F := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hZjet 0 (Nat.zero_le R))
  have hF : 0 ≤ F := (norm_nonneg _).trans (hYjet 0 (Nat.zero_le R))
  have hpair : ∀ U V : P × E → E,
      ContDiffOn ℝ (⊤ : ℕ∞) U S → ContDiffOn ℝ (⊤ : ℕ∞) V S →
      ∀ C D : ℝ, (∀ j ≤ R, ‖iteratedFDeriv ℝ j U p‖ ≤ C) →
        (∀ j ≤ R, ‖iteratedFDeriv ℝ j V p‖ ≤ D) →
      ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ (fun x => V (q.1, x)) q.2 (U q)) p‖ ≤
        2 ^ n * D * C := by
    intro U V hU hV C D hUjet hVjet
    have hD : 0 ≤ D := (norm_nonneg _).trans (hVjet 0 (Nat.zero_le R))
    apply (norm_joint_spatial_derivative_jet_le hS hU hV hp n).trans
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * D * C := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        gcongr
        · exact hVjet (j + 1) (by omega)
        · exact hUjet (n - j) (by omega)
      _ = _ := by
        simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        rfl
  have hYZ := ((partial_spatial_fderiv_contDiffOn hS hY).clm_apply hZ).contDiffAt
    (hS.mem_nhds hp)
  have hZY := ((partial_spatial_fderiv_contDiffOn hS hZ).clm_apply hY).contDiffAt
    (hS.mem_nhds hp)
  change ‖iteratedFDeriv ℝ n ((fun q => fderiv ℝ (fun x => Y (q.1, x)) q.2 (Z q)) -
    (fun q => fderiv ℝ (fun x => Z (q.1, x)) q.2 (Y q))) p‖ ≤ _
  rw [iteratedFDeriv_sub_apply (hYZ.of_le (by simp)) (hZY.of_le (by simp))]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (hpair Z Y hZ hY B F hZjet hYjet)
    (hpair Y Z hY hZ F B hYjet hZjet)).trans_eq
  rw [pow_succ]
  ring

end RothschildStein.G4

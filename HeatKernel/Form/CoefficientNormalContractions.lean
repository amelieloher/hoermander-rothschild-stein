-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoefficientContractions
public import HeatKernel.Form.NormalContractions
public import HeatKernel.Form.LipschitzCompositionLimits
public import HeatKernel.Form.ClosedConvexLift
public import HeatKernel.Form.QuadraticSublevels
import Mathlib.Tactic.Linter

/-! # Normal contractions for measurable elliptic horizontal forms -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal

namespace HeatKernel

/-- Normal contractions preserve the common global energy domain and decrease the energy
of every bounded measurable symmetric positive matrix coefficient field. -/
theorem exists_energyGraph_comp_normalContraction_coefficient {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (a : Fin q → Fin q → (Fin N → ℝ) → ℝ) {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume)
    (hsym : ∀ᵐ x ∂volume, ∀ i j, a i j x = a j i x)
    (hbound : ∀ᵐ x ∂volume, ∀ ξ : Fin q → ℝ,
      lower * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ)
    (v : energyGraph (N := N) ⊤ X) {η : ℝ → ℝ}
    (hη : LipschitzWith 1 η) (hzero : η 0 = 0) :
    ∃ z : energyGraph (N := N) ⊤ X,
      energyInclusion ⊤ X z = hη.compLp hzero (energyInclusion ⊤ X v) ∧
      coefficientEnergy ⊤ X a z z ≤ coefficientEnergy ⊤ X a v v := by
  let U : Opens (Fin N → ℝ) := ⊤
  have ha' : ∀ i j, AEStronglyMeasurable (a i j) (volume.restrict (U : Set (Fin N → ℝ))) := by
    simpa only [U, Opens.coe_top, Measure.restrict_univ] using ha
  have hs' : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ∀ i j, a i j x = a j i x := by
    simpa only [U, Opens.coe_top, Measure.restrict_univ] using hsym
  have hb' : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ∀ ξ : Fin q → ℝ,
      lower * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ := by
    simpa only [U, Opens.coe_top, Measure.restrict_univ] using hbound
  obtain ⟨b, hb, hb0, hbd, hbt⟩ := exists_smooth_contraction_approximation hη hzero
  have hLip : ∀ n, LipschitzWith 1 (b n) := fun n =>
    lipschitzWith_of_nnnorm_deriv_le ((hb n).differentiable (by simp))
      (fun s => by exact_mod_cast hbd n s)
  choose w hwf hwg hwe using fun n =>
    exists_energyGraph_comp_contDiff_one_energy_le X hX v ((hb n).of_le (by simp)) (hb0 n)
      (C := 1) (by simpa using hbd n)
  have hwf' : ∀ n, (w n : GradientSpace U q).fst =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => b n ((v : GradientSpace U q).fst x) := by
    simpa only [U, Opens.coe_top, Measure.restrict_univ] using hwf
  have hfnorm : ∀ n, ‖energyInclusion U X (w n)‖ ≤ ‖energyInclusion U X v‖ := by
    intro n
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hwf' n] with x hx
    change ‖(w n : GradientSpace U q).fst x‖ ≤ ‖(v : GradientSpace U q).fst x‖
    rw [hx]
    simpa only [hb0, dist_zero_right, NNReal.coe_one, one_mul] using
      (hLip n).dist_le_mul ((v : GradientSpace U q).fst x) 0
  have hgnorm : ∀ n, ‖energyGradient U X (w n)‖ ≤ ‖energyGradient U X v‖ := by
    intro n
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [NNReal.coe_one, one_pow, one_mul, horizontalEnergy,
      real_inner_self_eq_norm_sq] using hwe n
  have hlim := tendsto_L2_of_contraction_pointwise (energyInclusion U X v)
    hLip hb0 hη hzero hbt hwf'
  let B := coefficientEnergyContinuousBilinear U X a hlower ha' hs' hb' hupper
  have hBsym : ∀ u v, B u v = B v u := fun u v =>
    coefficientEnergy_symm U X a u v (fun i j => hs'.mono fun _ hx => hx i j)
  have hBpos : ∀ u, 0 ≤ B u u := fun u =>
    (mul_nonneg hlower (horizontalEnergy_self_nonneg U X u)).trans
      (coefficientEnergy_self_bounds U X a u hlower ha' hs' hb').1
  have hmem : ∀ n, w n ∈ {u | B u u ≤ B v v} := by
    intro n
    apply coefficientEnergy_self_le_of_scalar_gradient U X a hlower ha' hs' hb' v (w n)
      (fun x => deriv (b n) ((v : GradientSpace U q).fst x))
    · exact Eventually.of_forall fun x => hbd n _
    · simpa only [U, Opens.coe_top, Measure.restrict_univ] using hwg n
  let : InnerProductSpace ℝ (energyGraph U X) :=
    { (inferInstance : InnerProductSpace ℝ (energyGraph U X)) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (energyGraph U X)) }
  let : InnerProductSpace ℝ (SpatialL2 U) :=
    { (inferInstance : InnerProductSpace ℝ (SpatialL2 U)) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (SpatialL2 U)) }
  obtain ⟨z, hz, _, he⟩ := exists_lift_of_tendsto_of_bounded_mem_closed_convex
    (energyInclusion U X) w
    (fun n => energyGraph_norm_le_add_of_bounds U X (w n) (norm_nonneg _) (norm_nonneg _)
      (hfnorm n) (hgnorm n))
    (convex_bilinear_self_sublevel B hBsym hBpos (B v v))
    (isClosed_bilinear_self_sublevel B (B v v)) hmem hlim
  exact ⟨z, hz, he⟩



end HeatKernel

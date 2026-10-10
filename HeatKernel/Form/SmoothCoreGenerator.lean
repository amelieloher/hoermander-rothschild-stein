-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.WeakFormOperator
public import HeatKernel.Form.WeakGradientIntegration
public import HeatKernel.Form.CompactZeroBoundary
import Mathlib.Tactic.Linter

/-! # The positive form operator on smooth compact scalar functions -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- For smooth divergence-free horizontal fields, the positive form operator on the smooth
compact core is the negative sum of squared fields. The identity holds against every vector
of the closed energy domain. -/
theorem exists_smooth_core_operatorValue {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (ht : ∀ i (φ : (Fin N → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → ∀ x,
      fieldTranspose (X i) φ x = -fieldDerivative (X i) φ x)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ u : energyGraph (N := N) ⊤ X, ∃ g : SpatialL2 (N := N) ⊤,
      ((u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f) ∧
      (g =ᵐ[volume] (fun x => -(∑ i, fieldDerivative (X i) (fieldDerivative (X i) f) x))) ∧
      IsWeakFormOperatorValue (energyInclusion ⊤ X) (horizontalEnergy ⊤ X) u g := by
  let D : Fin q → (Fin N → ℝ) → ℝ := fun i => fieldDerivative (X i) f
  let DD : Fin q → (Fin N → ℝ) → ℝ := fun i => fieldDerivative (X i) (D i)
  have hD := fun i => contDiff_hasCompactSupport_fieldDerivative (hX i) hf hc
  have hDD := fun i => contDiff_hasCompactSupport_fieldDerivative (hX i) (hD i).1 (hD i).2
  have hp : ∀ i, MemLp (DD i) 2 volume := fun i =>
    (hDD i).1.continuous.memLp_of_hasCompactSupport (hDD i).2
  have hg : MemLp (fun x => -(∑ i, DD i x)) 2
      (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))) := by
    simpa only [Pi.neg_def, Opens.coe_top, Measure.restrict_univ] using
      (memLp_finsetSum Finset.univ (fun i _ => hp i)).neg
  let g := hg.toLp (fun x => -(∑ i, DD i x))
  have hgf : g =ᵐ[volume] (fun x => -(∑ i, DD i x)) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hg.coeFn_toLp
  obtain ⟨w, hw, hwf, hwD⟩ := exists_interiorGradientPair ⊤ X hf hc (subset_univ _) hX
  let u : energyGraph (N := N) ⊤ X :=
    ⟨w, zeroBoundaryGraph_le_energyGraph ⊤ X (interiorGradientPairs_subset_zeroBoundaryGraph ⊤ X hw)⟩
  refine ⟨u, g, hwf, hgf, ?_⟩
  intro v
  have hvp : MemLp ((v : GradientSpace (N := N) ⊤ q).fst : (Fin N → ℝ) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (v : GradientSpace (N := N) ⊤ q).fst
  have hi : ∀ i, Integrable (fun x => (v : GradientSpace (N := N) ⊤ q).fst x * DD i x) volume :=
    fun i => hvp.integrable_mul (hp i)
  have he : horizontalEnergy ⊤ X u v =
      ∑ i, ∫ x, (v : GradientSpace (N := N) ⊤ q).snd i x * D i x := by
    rw [horizontalEnergy_eq_integral_density]
    simp only [horizontalEnergyDensity, Opens.coe_top, Measure.restrict_univ]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [hwD i] with x hx
      simp only [u, hx, D, mul_comm]
    · intro i _
      simpa only [Pi.mul_def, Opens.coe_top, Measure.restrict_univ] using
        (Lp.memLp ((u : GradientSpace (N := N) ⊤ q).snd i)).integrable_mul
          (Lp.memLp ((v : GradientSpace (N := N) ⊤ q).snd i))
  have hb : ∀ i, (∫ x, (v : GradientSpace (N := N) ⊤ q).snd i x * D i x) =
      -(∫ x, (v : GradientSpace (N := N) ⊤ q).fst x * DD i x) := fun i =>
    integral_energyGradient_mul_test X hX v i (hD i).1 (hD i).2 (ht i (D i) (hD i).1)
  rw [he]
  simp_rw [hb]
  rw [Finset.sum_neg_distrib, L2.inner_def]
  simp only [Opens.coe_top, Measure.restrict_univ]
  calc
    -(∑ i, ∫ x, (v : GradientSpace (N := N) ⊤ q).fst x * DD i x) =
        ∫ x, -((v : GradientSpace (N := N) ⊤ q).fst x * ∑ i, DD i x) := by
      simp only [Finset.mul_sum, integral_neg, integral_finsetSum Finset.univ (fun i _ => hi i)]
    _ = ∫ x, inner ℝ (g x) (energyInclusion ⊤ X v x) := by
      apply integral_congr_ae
      filter_upwards [hgf] with x hx
      simp only [hx, energyInclusion_apply, RCLike.inner_apply, conj_trivial]
      ring



end HeatKernel

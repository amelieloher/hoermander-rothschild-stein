-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionLinearity

/-! # Scalar multiples of local weak parabolic solutions -/

@[expose] public section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Scalar multiplication preserves compact-cylinder energy bounds. -/
theorem HasLocalParabolicEnergyBounds.const_mul {N q : ℕ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hu : HasLocalParabolicEnergyBounds I U u g) (c : ℝ) :
    HasLocalParabolicEnergyBounds I U (fun t x => c * u t x)
      (fun i t x => c * g i t x) := by
  intro J K hJ hJI hK hKU
  obtain ⟨hub, hug⟩ := hu J K hJ hJI hK hKU
  refine ⟨?_, fun i => (hug i).const_mul c⟩
  apply lt_of_le_of_lt _ (ENNReal.mul_lt_top (by simp : ‖c‖ₑ < ⊤) hub)
  refine essSup_le_of_ae_le _ ?_ (by isBoundedDefault)
  filter_upwards [ENNReal.ae_le_essSup (fun t => eLpNorm (u t) 2 (volume.restrict K))]
    with t ht
  change eLpNorm (c • u t) 2 (volume.restrict K) ≤ _
  exact eLpNorm_const_smul_le.trans (mul_le_mul_of_nonneg_left ht bot_le)

/-- Scalar multiplication preserves the spacetime test identity. -/
theorem SatisfiesParabolicTestIdentity.const_mul {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hu : SatisfiesParabolicTestIdentity X a I U u g) (c : ℝ) :
    SatisfiesParabolicTestIdentity X a I U (fun t x => c * u t x)
      (fun i t x => c * g i t x) := by
  intro φ hφ hc hs
  obtain ⟨hui, hue⟩ := hu φ hφ hc hs
  have he : (fun z : ℝ × (Fin N → ℝ) =>
      -(c * u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * (c * g j z.1 z.2) * fderiv ℝ φ z (0, X i z.2)) =
      (fun z => c * (-(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2))) := by
    funext z
    have hp : (∑ i, ∑ j, a z.1 z.2 i j * (c * g j z.1 z.2) *
        fderiv ℝ φ z (0, X i z.2)) =
        c * (∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hp]
    ring
  change Integrable (fun z : ℝ × (Fin N → ℝ) =>
      -(c * u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
        ∑ i, ∑ j, a z.1 z.2 i j * (c * g j z.1 z.2) * fderiv ℝ φ z (0, X i z.2)) ∧ _
  rw [he]
  exact ⟨hui.const_mul c, by rw [integral_const_mul, hue, mul_zero]⟩

/-- Every scalar multiple of a local weak solution is a local weak solution. -/
theorem IsLocalWeakSolution.const_mul {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)} {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) (c : ℝ) :
    IsLocalWeakSolution G hq hqpos hw hspan a I U (fun t x => c * u t x) := by
  obtain ⟨hum, g, hgw, hge, hgt⟩ := hu
  refine ⟨hum.const_mul c, fun i t x => c * g i t x, ?_,
    HasLocalParabolicEnergyBounds.const_mul hge c,
    SatisfiesParabolicTestIdentity.const_mul hgt c⟩
  filter_upwards [hgw] with t ht
  exact fun i => S.hasWeakWordDeriv_smul (G.horizontalFields hq) U (ht i) c

end HeatKernel

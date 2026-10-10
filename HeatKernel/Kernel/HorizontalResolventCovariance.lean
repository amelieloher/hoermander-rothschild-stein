-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.FormGraphCovariance
public import HeatKernel.Kernel.FormPullbackInclusions
public import HeatKernel.Kernel.ResolventGraphCovariance

/-! # Translation and dilation of the horizontal form resolvent

The complete horizontal form actions give concrete covariance of the
associated real operator graph. Translation commutes with the resolvent,
and normalized dilation gives its affine parameter identity.
-/

@[expose] public section

noncomputable section

open RothschildStein

namespace HeatKernel

/-- Left translation preserves the operator graph of the global horizontal form. -/
theorem inverseResolventGraph_horizontalForm_leftTranslation {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (y : Fin N → ℝ)
    {u g : SpatialL2 (N := N) ⊤}
    (hu : InverseResolventGraph (horizontalFormResolvent ⊤ (G.horizontalFields hq)) u g) :
    InverseResolventGraph (horizontalFormResolvent ⊤ (G.horizontalFields hq))
      (spatialLeftTranslation G y u) (spatialLeftTranslation G y g) := by
  simpa only [one_smul] using inverseResolventGraph_horizontalForm_of_energy_covariance
    ⊤ (G.horizontalFields hq) (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)
    (spatialLeftTranslation G y) (energyLeftTranslationEquiv G hq y) 1
    (energyInclusion_energyLeftTranslation_eq_spatial G hq y)
    (inner_spatialLeftTranslation G y)
    (fun v w => by
      change horizontalEnergy ⊤ (G.horizontalFields hq) (energyLeftTranslation G hq y v)
        (energyLeftTranslation G hq y w) = 1 * horizontalEnergy ⊤ (G.horizontalFields hq) v w
      simpa only [one_mul] using horizontalEnergy_energyLeftTranslation G hq y v w) hu

/-- Normalized dilation scales the horizontal operator graph by the square of its factor. -/
theorem inverseResolventGraph_horizontalForm_normalizedDilation {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    {u g : SpatialL2 (N := N) ⊤}
    (hu : InverseResolventGraph (horizontalFormResolvent ⊤ (G.horizontalFields hq)) u g) :
    InverseResolventGraph (horizontalFormResolvent ⊤ (G.horizontalFields hq))
      (spatialNormalizedDilation G hr u) (r ^ 2 • spatialNormalizedDilation G hr g) :=
  inverseResolventGraph_horizontalForm_of_energy_covariance
    ⊤ (G.horizontalFields hq) (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)
    (spatialNormalizedDilation G hr) (normalizedEnergyDilationEquiv G hq hw hr) (r ^ 2)
    (energyInclusion_normalizedEnergyDilation_eq_spatial G hq hw hr)
    (inner_spatialNormalizedDilation G hr)
    (horizontalEnergy_normalizedEnergyDilation G hq hw hr) hu

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.GroupInteriorApproximation
public import RothschildStein.Definitions.fieldDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped Topology ENNReal
namespace HeatKernel

/-- Local commutation with group convolution transfers Lp convergence to field derivatives.
The commutation identity is an explicit hypothesis, including the locality of zero extension. -/
theorem tendsto_fieldDerivative_groupRegularize_of_local_commutation
    {N : ℕ} (G : HomogeneousGroup N) {ν : G2.HomogeneousNorm G}
    (φ : G2.GroupMollifier G ν) (Ω : Opens (Fin N → ℝ))
    {D : Set (Fin N → ℝ)} (hD : MeasurableSet D) (hDΩ : D ⊆ Ω)
    {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {f g : (Fin N → ℝ) → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ))))
    (hcomm : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ x ∂volume.restrict D,
      fieldDerivative V
        (G2.groupRegularize G φ ((Ω : Set (Fin N → ℝ)).indicator f) ε) x =
      G2.groupRegularize G φ ((Ω : Set (Fin N → ℝ)).indicator g) ε x) :
    Tendsto (fun ε : ℝ => eLpNorm
      (fun x => fieldDerivative V
        (G2.groupRegularize G φ ((Ω : Set (Fin N → ℝ)).indicator f) ε) x - g x)
      (ENNReal.ofReal p) (volume.restrict D)) (𝓝[>] 0) (𝓝 0) := by
  apply (tendsto_groupRegularize_zeroExtension_local G φ Ω hD hDΩ hp hg).congr'
  filter_upwards [hcomm] with ε hε
  apply eLpNorm_congr_ae
  filter_upwards [hε] with x hx
  rw [hx]

end HeatKernel

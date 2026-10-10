-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.ParabolicDualTimeBalance
public import HeatKernel.Bridge.DualEnergyPair
import Mathlib.Tactic.Linter

/-! # Local dual energy curves with their weak time balance -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Local energy bounds and the stationary identity yield compatible dual value
and flux curves on a compact cylinder, with their Bochner weak time equation. -/
theorem HasStationaryEnergyTestIdentity.exists_balanced_dual_curves {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ}
    {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hb : HasLocalParabolicEnergyBounds I U u g)
    (he : HasStationaryEnergyTestIdentity X a I U u g)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j))
    {C : ℝ} (hentry : ∀ i j, ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume, ‖a z.1 z.2 i j‖ ≤ C)
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    (V : Opens (Fin N → ℝ)) (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    (hu : MemLp (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2
      ((volume.restrict J).prod (volume.restrict K))) :
    ∃ D F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ),
      IsDualEnergyPair (E := zeroBoundaryGraph V X) J
        (fun t v => ∫ x, u t x * (v : GradientSpace (N := N) ⊤ q).fst x)
        (fun t v => ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
          (v : GradientSpace (N := N) ⊤ q).snd i x) D F := by
  obtain ⟨D, hD, hDr⟩ := exists_localized_dual_value_curve V X hK.measurableSet hVK
    (fun z => u z.1 z.2) hu
  obtain ⟨F, hF, hFr⟩ := hb.exists_zeroBoundary_dual_flux_curve
    X a ha hentry hJ hJI hK hKU V hVK
  exact ⟨D, F, hD, hF, hDr, hFr,
    he.dual_time_balance hJ hJI hK hKU V hVK D F hD hF hDr hFr⟩

end HeatKernel

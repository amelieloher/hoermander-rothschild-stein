-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CompactReferenceInjectivity
public import RothschildStein.G4.NearbyWeightedChartInjectivity
public import RothschildStein.G4.FixedRadiusSuboptimality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Function
open scoped Topology

namespace RothschildStein.G4

/-- Construct the exact reference-neighborhood package from
actual joint chart-derivative continuity, actual local spatial regularity
and actual nonzero reference Jacobians. The frame is chosen optimal at
small scales at the fixed point; nearby suboptimality is asserted only
at its fixed reference radius (BB (9.52)–(9.55), pp. 453–454). -/
theorem referenceChartNeighborhoods_of_actual_derivative_continuity
    {P : Type*} [TopologicalSpace P] {m n : ℕ} {K : Set P}
    (w : Fin m → ℕ+) (Z : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (F : P → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (x : P → (Fin n → ℝ)) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hZ : ∀ J, Continuous (fun p => Z p J (x p)))
    (hspan : ∀ p ∈ K, ∃ B : Fin n → Fin m, frameDet (Z p) B (x p) ≠ 0)
    (hlocal : ∀ p ∈ K, ∀ B : Fin n → Fin m,
      ∀ᶠ q : (Fin n → ℝ) × P in 𝓝 (0, p), DifferentiableAt ℝ (F q.2 B 0) q.1)
    (hder : ∀ p ∈ K, ∀ B : Fin n → Fin m,
      ContinuousAt (fun q : (Fin n → ℝ) × P => fderiv ℝ (F q.2 B 0) q.1) (0, p))
    (hjac : ∀ p ∈ K, ∀ B R, 0 < R → R ≤ 1 → IsSuboptimal (Z p) w B (x p) 1 R →
      Matrix.det (coordinateDerivativeMatrix (fderiv ℝ (F p B 0) 0)) ≠ 0) :
    ReferenceChartNeighborhoods K w Z F x t := by
  intro p hp
  obtain ⟨B, hB, R, hR, hR1, hopt⟩ := exists_small_scale_optimal_frame (Z p) w (x p) (hspan p hp)
  have hoptimal := hopt R hR le_rfl
  have hdet := hjac p hp B R hR hR1 hoptimal
  have hinj : Injective (fderiv ℝ (F p B 0) 0) := by
    have hunit : IsUnit (coordinateDerivativeMatrix (fderiv ℝ (F p B 0) 0)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    intro u v huv
    apply Matrix.mulVec_injective_iff_isUnit.mpr hunit
    simpa only [coordinateDerivativeMatrix_mulVec] using huv
  let L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (F p B 0) 0).toLinearMap hinj).toContinuousLinearEquiv
  have hL : (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ (F p B 0) 0 := by
    ext u
    rfl
  obtain ⟨α, hα, hα1, V, hV, hVinj⟩ := exists_nearby_injective_weighted_boxes (w ∘ B)
    (fun q => F q B 0) p L (hlocal p hp B) (hder p hp B) hL.symm
  have hsub := eventually_suboptimal_of_fixed_radius_optimal Z x w p B ht ht1 hR hZ hB hoptimal
  let U := V ∩ {q : P | IsSuboptimal (Z q) w B (x q) t R}
  have hU : U ∈ 𝓝 p := inter_mem hV hsub
  refine ⟨B, R, α, U, hR, hR1, hα, hα1, hU, ?_⟩
  intro q _hq hqU
  exact ⟨hqU.2, hVinj q hqU.1 R hR hR1⟩

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2CertificateCarrier
public import RothschildStein.P1.RightParametrixTransport
public import RothschildStein.S.DistanceGeometry

/-!
# Lifted distance geometry: the `(HD1)`-`(HD2)` package of the lifted control distance

For a lifted chart `C`, the ambient lifted control distance `C.dl = d̃_{X̃,Õ}` is an extended metric
on the chart domain `C.U` inducing the
Euclidean subspace topology. This is the `S.DistanceGeometry` package whose hypothesis the Hölder
extension statements of the gain theorem, the weak extension theorem and P2 carry (`G.d = C.dl`).

* `LiftedChart.distanceGeometry C : S.DistanceGeometry C.chartOpens`, with `d = C.dl`
  (`LiftedChart.distanceGeometry_d`): the metric is the carrier metric of the geometric certificate
  (`LiftedChart.carrierMetricSpace`; the topology comparison is `isOpen_iff_forall_carrierDist`, from
  the chart fields `gauge_comparison` and the homeomorphism `e η`), and the extended distance is
  finite on `C.U × C.U` (`dl_finite_on_U`), so `edist = ofReal (toReal d̃) = d̃`;
* `restrictDistanceGeometry`: the package restricts to every open `V ≤ Ω` with the same `d`
  (the induced extended metric; the topology is the induced one on both sides);
* `LiftedChart.distanceGeometryOn C V hV : S.DistanceGeometry V` for open `V ≤ C.chartOpens`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- **`(HD1)`-`(HD2)` for the lifted control distance.** On the chart domain
`C.chartOpens = C.U`, the lifted control distance `C.dl` is an extended metric inducing the Euclidean
subspace topology (BB Prop 1.41 and Thm 1.53, pp. 22-36, in the chart form of the carrier metric). -/
def distanceGeometry : S.DistanceGeometry C.chartOpens where
  d := C.dl
  metric := (inferInstance : MetricSpace C.Carrier).toEMetricSpace
  distance_eq := fun x y => by
    refine (edist_dist (α := C.Carrier) x y).trans ?_
    show ENNReal.ofReal (C.dl x.1 y.1).toReal = C.dl x.1 y.1
    exact ENNReal.ofReal_toReal (C.dl_finite_on_U x.2 y.2)
  topology_eq := rfl

end LiftedChart
end RothschildStein.P1

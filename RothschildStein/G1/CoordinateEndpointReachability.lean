-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.FiniteScheduleReachability
public import RothschildStein.G1.CoordinateEndpointChart
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.G1

/-- A finite coordinate endpoint chart preserves actual finite
primitive reachability near zero (BB p. 34). -/
theorem coordinateEndpointChart_eventually_path {m n k : ℕ}
    {Ω : Set (Fin n → ℝ)} (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (H : Fin k → ℝ × (Fin n → ℝ) → (Fin n → ℝ))
    (hz : ∀ i x, H i (0,x) = x) (S : List (Fin k)) (x : Fin n → ℝ)
    (hH : ∀ i, ContDiffAt ℝ 1 (H i) (0,x))
    (hp : ∀ i, ∀ᶠ q : ℝ × (Fin n → ℝ) in 𝓝 (0,x), FiniteGeneratorPath Ω X q.2 (H i q)) :
    ∀ᶠ q : (Fin k → ℝ) × (Fin n → ℝ) in 𝓝 (0,x),
      FiniteGeneratorPath Ω X q.2 (coordinateEndpointChart H S q) := by
  induction S with
  | nil => exact Filter.Eventually.of_forall (fun q => Relation.EqvGen.refl q.2)
  | cons i S ih =>
    have ht := (coordinateEndpointChart_contDiffAt_zero H hz S x hH).continuousAt
    have hh : ContinuousAt
        (fun q : (Fin k → ℝ) × (Fin n → ℝ) => (q.1 i,coordinateEndpointChart H S q)) (0,x) :=
      ((continuous_apply i).continuousAt.comp continuousAt_fst).prodMk ht
    have he := hh.tendsto.eventually (by
      simpa only [Pi.zero_apply,coordinateEndpointChart_zero H hz] using hp i)
    filter_upwards [ih,he] with q hq hi
    exact Relation.EqvGen.trans _ _ _ hq hi
end RothschildStein.G1

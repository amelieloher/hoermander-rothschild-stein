-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CoordinateEndpointChart
public import RothschildStein.G1.WeightedTriangle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace RothschildStein.G1

/-- Local costs of actual signed endpoints sum along the finite
coordinate chart. Joint continuity keeps the intermediate base points
inside the neighborhoods where those costs were proved (BB p. 35). -/
theorem coordinateEndpointChart_eventually_control_cost {m n k : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (H : Fin k → ℝ × (Fin n → ℝ) → (Fin n → ℝ))
    (hz : ∀ i x, H i (0, x) = x) (S : List (Fin k))
    (x : Fin n → ℝ) (hx : x ∈ Ω)
    (hH : ∀ i, ContDiffAt ℝ 1 (H i) (0, x))
    {L α : ℝ} (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hcost : ∀ i, ∀ᶠ p : ℝ × (Fin n → ℝ) in 𝓝 (0, x),
      controlDistance Ω w X p.2 (H i p) ≤ ENNReal.ofReal (L * |p.1| ^ α)) :
    ∀ᶠ q : (Fin k → ℝ) × (Fin n → ℝ) in 𝓝 (0, x),
      controlDistance Ω w X q.2 (coordinateEndpointChart H S q) ≤
        ENNReal.ofReal ((S.length : ℝ) * L * ‖q.1‖ ^ α) := by
  induction S with
  | nil =>
    have hm := (continuous_snd.continuousAt (x := ((0 : Fin k → ℝ), x))).preimage_mem_nhds (hΩ.mem_nhds hx)
    filter_upwards [hm] with q hq
    change controlDistance Ω w X q.2 q.2 ≤ _
    rw [controlDistance_self (Ω := Ω) w X (show q.2 ∈ Ω from hq)]
    exact bot_le
  | cons i S ih =>
    have htail := (coordinateEndpointChart_contDiffAt_zero H hz S x hH).continuousAt
    have hfirst : ContinuousAt
        (fun q : (Fin k → ℝ) × (Fin n → ℝ) => (q.1 i, coordinateEndpointChart H S q)) (0, x) :=
      ((continuous_apply i).continuousAt.comp continuousAt_fst).prodMk htail
    have hp : ∀ᶠ q : (Fin k → ℝ) × (Fin n → ℝ) in 𝓝 (0, x),
        controlDistance Ω w X (coordinateEndpointChart H S q)
          (H i (q.1 i, coordinateEndpointChart H S q)) ≤
          ENNReal.ofReal (L * |q.1 i| ^ α) := by
      have hm := hfirst.tendsto.eventually (by
        simpa only [Pi.zero_apply, coordinateEndpointChart_zero H hz] using hcost i)
      exact hm
    filter_upwards [ih, hp] with q hq hqi
    have hc : |q.1 i| ^ α ≤ ‖q.1‖ ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1 i) hα
    calc
      _ ≤ controlDistance Ω w X q.2 (coordinateEndpointChart H S q) +
          controlDistance Ω w X (coordinateEndpointChart H S q)
            (H i (q.1 i, coordinateEndpointChart H S q)) :=
        controlDistance_triangle Ω w X _ _ _
      _ ≤ ENNReal.ofReal ((S.length : ℝ) * L * ‖q.1‖ ^ α) +
          ENNReal.ofReal (L * ‖q.1‖ ^ α) :=
        add_le_add hq (hqi.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc hL)))
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

end RothschildStein.G1

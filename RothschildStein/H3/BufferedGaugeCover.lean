-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GaugeControlComparison
public import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.H3
open G2
variable {N m : ℕ} {G : HomogeneousGroup N}

/-- A compact set has a finite cover by smooth gauge balls with a uniform
buffer, under the global flow and metric-comparison hypotheses (BB p. 578). -/
theorem buffered_quasiBall_cover_of_controlNorm {w : Fin m → ℕ+}
    {Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G w Y) (ν : HomogeneousNorm G)
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hcmp : ∀ z, a * H.norm z ≤ ν z ∧ ν z ≤ A * H.norm z)
    {K V : Set (ControlCarrier N)} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ r θ : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < θ ∧ ∃ S : Finset K,
      (∀ x ∈ K, ∃ z ∈ S, x ∈ gaugeBall G ν z.1 (r / (2 * (A / a)))) ∧
      (∀ z ∈ S, gaugeBall G ν z.1 (2 * r) ⊆ V) ∧
      ∀ x ∈ K, ∀ y : ControlCarrier N,
        (controlDistance univ w Y x y).toReal < θ →
        ∃ z ∈ S, x ∈ gaugeBall G ν z.1 (r / (2 * (A / a))) ∧
          y ∈ gaugeBall G ν z.1 r := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G H.norm H.constant_one H.symmetric
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_thickening_subset_open hV hKV
  let r := min 1 (a * δ / 4)
  have hr : 0 < r := lt_min zero_lt_one (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrad : 2 * r / a < δ := by
    apply (div_lt_iff₀ ha).mpr
    have hb : r ≤ a * δ / 4 := min_le_right _ _
    nlinarith
  let C := A / a
  have hC : 0 < C := div_pos hA ha
  have hρ : 0 < r / (2 * C) := by positivity
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover
    (fun z : K => gaugeBall G ν z.1 (r / (2 * C)))
    (fun z => isOpen_gaugeBall G ν.gauge z.1 _)
    (by intro x hx; exact mem_iUnion.mpr ⟨⟨x, hx⟩, center_mem_gaugeBall G ν.gauge x hρ⟩)
  have hcover : ∀ x ∈ K, ∃ z ∈ S, x ∈ gaugeBall G ν z.1 (r / (2 * C)) := by
    intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hS hx)
    obtain ⟨hzS, hxz⟩ := mem_iUnion.mp hz
    exact ⟨z, hzS, hxz⟩
  refine ⟨r, r / (2 * C * A), hr, hr1, by positivity, S, hcover, ?_, ?_⟩
  · intro z _ y hy
    have hd := (quasiBall_control_comparison_of_controlNorm H ν ha hA hcmp z.1 (2 * r)).2 hy
    change (controlDistance univ w Y y z.1).toReal < 2 * r / a at hd
    rw [controlDistance_toReal_of_controlNorm G H y z.1] at hd
    have hb : y ∈ ball (z : ControlCarrier N) δ :=
      (show gaugeDistance G H.norm y z.1 < δ from hd.trans hrad)
    exact hδV (ball_subset_thickening z.property δ hb)
  · intro x hx y hy
    obtain ⟨z, hz, hxz⟩ := hcover x hx
    refine ⟨z, hz, hxz, ?_⟩
    have hy' : gaugeDistance G H.norm x y < r / (2 * C * A) := by
      rw [controlDistance_toReal_of_controlNorm G H (x : Fin N → ℝ) (y : Fin N → ℝ)] at hy
      exact hy
    have hxy : ν (G.mul (G.inv x) y) < A * (r / (2 * C * A)) := by
      have hb := (hcmp (G.mul (G.inv x) y)).2
      have he := (gaugeDistance_symmetric G H.norm H.symmetric y x).symm
      change H.norm (G.mul (G.inv x) y) = gaugeDistance G H.norm x y at he
      rw [he] at hb
      exact hb.trans_lt (mul_lt_mul_of_pos_left hy' hA)
    have htri := (smoothGauge_quasitriangle_of_controlNorm H ν ha hA hcmp).2
      (G.mul (G.inv z.1) x) (G.mul (G.inv x) y)
    have hmul : G.mul (G.mul (G.inv z.1) x) (G.mul (G.inv x) y) = G.mul (G.inv z.1) y := by
      calc
        _ = G.mul (G.inv z.1) (G.mul x (G.mul (G.inv x) y)) := G.assoc _ _ _
        _ = G.mul (G.inv z.1) (G.mul (G.mul x (G.inv x)) y) :=
          congrArg (G.mul (G.inv z.1)) (G.assoc x (G.inv x) y).symm
        _ = G.mul (G.inv z.1) y :=
          congrArg (G.mul (G.inv z.1))
            ((congrArg (fun v => G.mul v y) (G.inverse_right x)).trans (G.zero_left y))
    rw [hmul] at htri
    change ν (G.mul (G.inv z.1) x) < r / (2 * C) at hxz
    change ν (G.mul (G.inv z.1) y) < r
    have heq : C * (r / (2 * C) + A * (r / (2 * C * A))) = r := by
      field_simp [ne_of_gt hC, ne_of_gt hA]
      ring
    exact htri.trans_lt ((mul_lt_mul_of_pos_left (add_lt_add hxz hxy) hC).trans_eq heq)

end RothschildStein.H3

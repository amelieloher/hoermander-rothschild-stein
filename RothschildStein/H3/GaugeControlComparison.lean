-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HomogeneousBounds
public import RothschildStein.H3.GaugeGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
open G2
variable {N m : ℕ} {G : HomogeneousGroup N}

/-- The control-ball and quasi-ball inclusions under the global
control-norm and metric-comparison hypotheses (BB p. 578). -/
theorem quasiBall_control_comparison_of_controlNorm {w : Fin m → ℕ+}
    {Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G w Y) (ν : HomogeneousNorm G)
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hcmp : ∀ z, a * H.norm z ≤ ν z ∧ ν z ≤ A * H.norm z)
    (x : Fin N → ℝ) (r : ℝ) :
    {y | (controlDistance univ w Y y x).toReal < r / A} ⊆ gaugeBall G ν x r ∧
    gaugeBall G ν x r ⊆ {y | (controlDistance univ w Y y x).toReal < r / a} := by
  constructor
  · intro y hy
    change (controlDistance univ w Y y x).toReal < r / A at hy
    rw [controlDistance_toReal_of_controlNorm G H] at hy
    change H.norm (G.mul (G.inv x) y) < r / A at hy
    change ν (G.mul (G.inv x) y) < r
    exact (hcmp _).2.trans_lt (by nlinarith [(lt_div_iff₀ hA).mp hy])
  · intro y hy
    change (controlDistance univ w Y y x).toReal < r / a
    rw [controlDistance_toReal_of_controlNorm G H]
    change ν (G.mul (G.inv x) y) < r at hy
    change H.norm (G.mul (G.inv x) y) < r / a
    apply (lt_div_iff₀ ha).mpr
    nlinarith [(hcmp (G.mul (G.inv x) y)).1]

/-- The quasitriangle estimate has constant A/a under the smooth-gauge
flow and metric-comparison hypotheses. -/
theorem smoothGauge_quasitriangle_of_controlNorm {w : Fin m → ℕ+}
    {Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G w Y) (ν : HomogeneousNorm G)
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hcmp : ∀ z, a * H.norm z ≤ ν z ∧ ν z ≤ A * H.norm z) :
    1 ≤ A / a ∧ ∀ x y, ν (G.mul x y) ≤ (A / a) * (ν x + ν y) := by
  have hn (z : Fin N → ℝ) : H.norm z ≤ ν z / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using (hcmp z).1
  obtain ⟨_, ⟨z, hz⟩⟩ := homogeneousGauge_unitSphere H.norm.gauge
  have hbounds := hcmp z
  rw [hz, mul_one, mul_one] at hbounds
  refine ⟨(one_le_div ha).mpr (hbounds.1.trans hbounds.2), ?_⟩
  intro x y
  calc
    ν (G.mul x y) ≤ A * H.norm (G.mul x y) := (hcmp _).2
    _ ≤ A * (H.norm x + H.norm y) := mul_le_mul_of_nonneg_left
      (by simpa only [H.constant_one, one_mul] using H.norm.mul_le x y) hA.le
    _ ≤ A * (ν x / a + ν y / a) :=
      mul_le_mul_of_nonneg_left (add_le_add (hn x) (hn y)) hA.le
    _ = (A / a) * (ν x + ν y) := by ring

end RothschildStein.H3

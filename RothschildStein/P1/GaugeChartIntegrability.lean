-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ChartKernelIntegrability
public import RothschildStein.G2.LocalPower
public import RothschildStein.G2.MaxGauge
public import RothschildStein.P1.KernelEstimatesHomogeneous

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Every positive-type gauge power is integrable in the actual
chart variable on compact coordinate patches. -/
theorem LiftedChart.integrableOn_gauge_power_theta
    (C : LiftedChart w s Ω hΩ X x₀ m) (d : ℤ)
    (hd : -(C.G.homogeneousDimension : ℤ) < d)
    (ξ : Fin (n + m) → ℝ) (hξ : ξ ∈ C.U)
    (K : Set (Fin (n + m) → ℝ)) (hK : IsCompact K) (hKU : K ⊆ C.U) :
    IntegrableOn (fun η => kgauge C.G (C.Θ η ξ) ^ d) K := by
  have hdegree : -(d : ℝ) < C.G.homogeneousDimension := by
    have hc : -(C.G.homogeneousDimension : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hf := (G2.locallyIntegrable_power_iff (G2.isHomogeneousGauge_max C.G) (-(d : ℝ))).mpr hdegree
  have hf' : LocallyIntegrable (fun u : Fin (n + m) → ℝ => kgauge C.G u ^ d) volume := by
    simpa only [neg_neg, Real.rpow_intCast, kgauge] using hf
  exact C.integrableOn_modelKernel_comp_theta _ hf' ξ hξ K hK hKU

end RothschildStein.P1

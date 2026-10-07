-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalRadialEndpointFactor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.G1

/-- The actual radial factor's zero value is uniquely determined
at every base point and coefficient direction in its local domain. -/
theorem local_radial_factor_zero_value {m n : ℕ}
    (F : ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
    {V : Set ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)))} (hV : IsOpen V)
    (H : ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) → (Fin n → ℝ))
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H V)
    (he : ∀ q ∈ V, F (q.1 0 • q.2.1, q.2.2) - q.2.2 = q.1 0 • H q)
    (v₀ : Fin m → ℝ) (x₀ : Fin n → ℝ) (hV₀ : (0, (v₀, x₀)) ∈ V)
    (hslice : DifferentiableAt ℝ (fun z : Fin m → ℝ => F (z, x₀)) 0) :
    H (0, (v₀, x₀)) = fderiv ℝ (fun z => F (z, x₀)) 0 v₀ := by
  let q : ℝ → ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) :=
    fun t => (fun _ => t, (v₀, x₀))
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := (contDiff_pi.mpr (fun _ => contDiff_id)).prodMk contDiff_const
  have hHt : DifferentiableAt ℝ (fun t => H (q t)) 0 :=
    ((hH.contDiffAt (hV.mem_nhds hV₀)).comp (f := q) 0 hq.contDiffAt).differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => t • H (q t)) (H (q 0)) (0 : ℝ) := by
    convert (hasDerivAt_id (0 : ℝ)).smul hHt.hasDerivAt using 1 <;> first | rfl | simp
  have hv : HasDerivAt (fun t : ℝ => t • v₀) v₀ (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v₀
  have hd : HasDerivAt (fun t : ℝ => F (t • v₀, x₀) - x₀)
      (fderiv ℝ (fun z => F (z, x₀)) 0 v₀) (0 : ℝ) := by
    have hh : HasFDerivAt (fun z : Fin m → ℝ => F (z, x₀))
        (fderiv ℝ (fun z => F (z, x₀)) 0) ((fun t : ℝ => t • v₀) 0) := by
      simpa using hslice.hasFDerivAt
    convert (hh.comp_hasDerivAt (0 : ℝ) hv).sub (hasDerivAt_const (0 : ℝ) x₀) using 1 <;> first | rfl | simp
  have heq : (fun t => F (t • v₀, x₀) - x₀) =ᶠ[𝓝 0] (fun t => t • H (q t)) := by
    have hm := hq.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hV₀)
    filter_upwards [hm] with t ht
    exact he (q t) ht
  exact (hd.congr_of_eventuallyEq heq.symm).unique hp |>.symm

end RothschildStein.G1

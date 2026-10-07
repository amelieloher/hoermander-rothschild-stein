-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Locality
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- A continuous local function times an interior test is
continuous globally, without any condition on exterior values
(BB Thm 2.20, p. 86; cutoff extension). -/
theorem continuous_mul_test_of_continuousOn
    (Ω : Opens (Fin n → ℝ)) {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : Continuous (fun x => f x*φ x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
  · exact (hf.continuousAt (Ω.isOpen.mem_nhds hx)).mul φ.continuous.continuousAt
  · have hs : x ∉ tsupport φ := fun h => hx (φ.tsupport_subset h)
    have he : (fun y => f y*φ y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hs] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy,mul_zero]
    exact he.continuousAt

end RothschildStein.S

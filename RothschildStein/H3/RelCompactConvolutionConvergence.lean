-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ConvolutionConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
open G2

/-- Actual convolution convergence holds on every relatively
compact open set, using one containing norm ball for its compact closure. -/
theorem PositiveType.convolution_tendsto_relCompact {n : ℕ} {G : HomogeneousGroup n}
    {α : ℝ} {K F : (Fin n → ℝ) → ℝ} (hK : PositiveType G α K)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : ℕ → (Fin n → ℝ) → ℝ)
    (hF : MemLp F p volume) (hf : ∀ j, MemLp (f j) p volume)
    (hsF : ∀ᵐ y ∂volume, ρ ≤ ν y → F y = 0)
    (hsf : ∀ j, ∀ᵐ y ∂volume, ρ ≤ ν y → f j y = 0)
    (ht : Tendsto (fun j => eLpNorm (f j-F) p volume) atTop (𝓝 0))
    (U : Opens (Fin n → ℝ)) (hU : IsCompact (closure (U : Set (Fin n → ℝ)))) :
    MemLp (groupConvolution G F K) p (volume.restrict (U : Set (Fin n → ℝ))) ∧
      (∀ j, MemLp (groupConvolution G (f j) K) p (volume.restrict (U : Set (Fin n → ℝ)))) ∧
      Tendsto (fun j => eLpNorm (groupConvolution G (f j) K-groupConvolution G F K)
        p (volume.restrict (U : Set (Fin n → ℝ)))) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := hU.exists_bound_of_continuousOn ν.gauge.1.continuousOn
  let R := max C 0+1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hUR : (U : Set (Fin n → ℝ)) ⊆ {x | ν x < R} := by
    intro x hx
    have hb := hC x (subset_closure hx)
    have hn : ν x ≤ |ν x| := le_abs_self _
    have hm : C ≤ max C 0 := le_max_left _ _
    change ν x < max C 0+1
    rw [Real.norm_eq_abs] at hb
    linarith
  have hh := hK.local_convolution_tendsto ν h1 hsym hρ hR hp f hF hf hsF hsf ht
  have hμ := Measure.restrict_mono_set volume hUR
  refine ⟨hh.1.mono_measure hμ,fun j => (hh.2.1 j).mono_measure hμ,?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh.2.2
    (fun _ => bot_le) (fun j => eLpNorm_mono_measure _ hμ)

end RothschildStein.H3

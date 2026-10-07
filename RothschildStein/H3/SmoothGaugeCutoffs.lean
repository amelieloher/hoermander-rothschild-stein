-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GaugeGeometry
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- A smooth scalar profile constant near zero gives a globally
smooth gauge cutoff, even though the gauge is smooth only off zero (BB p. 578). -/
theorem contDiff_gauge_cutoff {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hs : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ (ν x / ε)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    have hz : ν (0 : Fin N → ℝ) < ε / 2 := by
      rw [(hν.2.2.1 0).mpr rfl]
      positivity
    filter_upwards [hν.1.continuousAt.eventually (gt_mem_nhds hz)] with y hy
    apply hone
    apply (div_le_iff₀ hε).mpr
    linarith
  · have hn := hs.contDiffAt (isOpen_compl_singleton.mem_nhds
      (show x ∈ ({0}ᶜ : Set (Fin N → ℝ)) from hx))
    exact hφ.contDiffAt.comp x (hn.div_const ε)

/-- Cutting off the singularity makes a punctured smooth kernel
smooth on the whole carrier; no value of the original kernel at zero is used. -/
theorem contDiff_kernel_exterior_cutoff {ν F : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hs : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (1 - φ (ν x / ε)) * F x) := by
  have hcut := contDiff_gauge_cutoff hν hs hφ hone hε
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hz : ν (0 : Fin N → ℝ) < ε / 2 := by
      rw [(hν.2.2.1 0).mpr rfl]
      positivity
    filter_upwards [hν.1.continuousAt.eventually (gt_mem_nhds hz)] with y hy
    rw [hone _ ((div_le_iff₀ hε).mpr (by linarith)), sub_self]
    ring
  · exact (contDiffAt_const.sub hcut.contDiffAt).mul
      (hF.contDiffAt (isOpen_compl_singleton.mem_nhds
        (show x ∈ ({0}ᶜ : Set (Fin N → ℝ)) from hx)))

end RothschildStein.H3

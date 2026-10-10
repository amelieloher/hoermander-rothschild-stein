-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HilbertOrbitTests
public import HeatKernel.Kernel.L2Differentiation
public import HeatKernel.Kernel.L2Continuity
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Compact scalar families as Hilbert-space time tests

Scalar families supported in a compact time set give compactly supported
L² curves. Their L² derivatives can be inserted directly in the integrated
Hilbert-space product rule.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Topology

namespace HeatKernel

/-- An almost-everywhere vanishing scalar slice defines the zero L² class. -/
theorem toLp_two_eq_zero_of_ae_eq_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) (hz : f =ᵐ[μ] 0) :
    hf.toLp f = 0 := by
  apply Lp.ext
  exact (hf.coeFn_toLp.trans hz).trans (Lp.coeFn_zero ℝ 2 μ).symm

/-- A closed time set supporting the scalar slices also supports their L² classes. -/
theorem tsupport_toLp_two_subset {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : ℝ → α → ℝ) (hf : ∀ t, MemLp (f t) 2 μ)
    {K : Set ℝ} (hK : IsClosed K) (hz : ∀ t ∉ K, f t =ᵐ[μ] 0) :
    tsupport (fun t => (hf t).toLp (f t)) ⊆ K := by
  apply closure_minimal _ hK
  intro t ht
  by_contra hnot
  exact ht (toLp_two_eq_zero_of_ae_eq_zero (hf t) (hz t hnot))

/-- A compact scalar L² family supplies the time test in the weak Hilbert-space orbit identity. -/
theorem integral_inner_orbit_scalar_time_test_eq_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (I : Opens ℝ) (u ψ : ℝ → Lp ℝ 2 μ)
    (f d : ℝ → α → ℝ) (hf : ∀ t, MemLp (f t) 2 μ) (hd : ∀ t, MemLp (d t) 2 μ)
    (hu : ContDiffOn ℝ 1 u (I : Set ℝ))
    (hderiv : ∀ t, HasDerivAt (fun s => (hf s).toLp (f s)) ((hd t).toLp (d t)) t)
    (hc : Continuous (fun t => (hd t).toLp (d t)))
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ I)
    (hz : ∀ t ∉ K, f t =ᵐ[μ] 0)
    (hpair : ∀ t, inner ℝ (deriv u t) ((hf t).toLp (f t)) = inner ℝ (u t) (ψ t)) :
    Integrable (fun t => inner ℝ (u t) ((hd t).toLp (d t) + ψ t)) ∧
      (∫ t, inner ℝ (u t) ((hd t).toLp (d t) + ψ t)) = 0 := by
  have heq : deriv (fun t => (hf t).toLp (f t)) = fun t => (hd t).toLp (d t) := by
    funext t
    exact (hderiv t).deriv
  have hC : ContDiff ℝ 1 (fun t => (hf t).toLp (f t)) := by
    apply contDiff_one_iff_deriv.mpr
    exact ⟨fun t => (hderiv t).differentiableAt, heq.symm ▸ hc⟩
  have hs := tsupport_toLp_two_subset f hf hK.isClosed hz
  have hcompact : HasCompactSupport (fun t => (hf t).toLp (f t)) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hs
  simpa only [heq] using integral_inner_orbit_weak_test_eq_zero I u
    (fun t => (hf t).toLp (f t)) ψ hu hC hcompact (hs.trans hKI) hpair

end HeatKernel

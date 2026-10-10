-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import HeatKernel.Moser.StationaryWeakIdentity

/-! # Compact Hilbert-space tests of smooth orbits

A compact test supported in the differentiability domain makes its scalar
pairing with an orbit globally continuously differentiable. Integration of
the product rule gives the weak time identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Scalar pairing with a compact test has no support outside that test. -/
theorem tsupport_inner_subset_right {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u φ : ℝ → H) :
    tsupport (fun t => inner ℝ (u t) (φ t)) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro t ht
  by_contra hnot
  exact ht (by
    change inner ℝ (u t) (φ t) = 0
    rw [image_eq_zero_of_notMem_tsupport hnot, inner_zero_right])

/-- An orbit continuously differentiable on a domain has a continuously differentiable pairing with compact tests. -/
theorem contDiff_inner_compact_test {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (I : Opens ℝ) (u φ : ℝ → H)
    (hu : ContDiffOn ℝ 1 u (I : Set ℝ)) (hφ : ContDiff ℝ 1 φ)
    (hs : tsupport φ ⊆ I) :
    ContDiff ℝ 1 (fun t => inner ℝ (u t) (φ t)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t ∈ I
  · exact (hu.contDiffAt (I.isOpen.mem_nhds ht)).inner ℝ hφ.contDiffAt
  · have hnot : t ∉ tsupport φ := fun h => ht (hs h)
    have hzero : (fun s => inner ℝ (u s) (φ s)) =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hnot] with s hs
      rw [image_eq_zero_of_notMem_tsupport hs, inner_zero_right]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- The integrated Hilbert-space product rule vanishes for compact tests inside the smoothness domain. -/
theorem integral_inner_orbit_deriv_test_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (I : Opens ℝ) (u φ : ℝ → H)
    (hu : ContDiffOn ℝ 1 u (I : Set ℝ)) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ I) :
    Integrable (fun t => inner ℝ (u t) (deriv φ t) + inner ℝ (deriv u t) (φ t)) ∧
      (∫ t, inner ℝ (u t) (deriv φ t) + inner ℝ (deriv u t) (φ t)) = 0 := by
  let g : ℝ → ℝ := fun t => inner ℝ (u t) (φ t)
  have hg : ContDiff ℝ 1 g := contDiff_inner_compact_test I u φ hu hφ hs
  have hgc : HasCompactSupport g :=
    hc.of_isClosed_subset (isClosed_tsupport g) (tsupport_inner_subset_right u φ)
  have heq : deriv g = fun t => inner ℝ (u t) (deriv φ t) +
      inner ℝ (deriv u t) (φ t) := by
    funext t
    by_cases ht : t ∈ I
    · exact (((hu.contDiffAt (I.isOpen.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt.inner
        ℝ ((hφ.differentiable (by norm_num) t).hasDerivAt)).deriv
    · have hnot : t ∉ tsupport φ := fun h => ht (hs h)
      have hnotg : t ∉ tsupport g := fun h => hnot (tsupport_inner_subset_right u φ h)
      rw [deriv_of_notMem_tsupport hnotg, deriv_of_notMem_tsupport hnot,
        image_eq_zero_of_notMem_tsupport hnot, inner_zero_right, inner_zero_right, add_zero]
  rw [← heq]
  exact ⟨(hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hgc.deriv,
    integral_deriv_eq_zero_of_hasCompactSupport hg hgc⟩

/-- A generator pairing identity supplies the weak orbit identity against compact time-dependent tests. -/
theorem integral_inner_orbit_weak_test_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (I : Opens ℝ) (u φ ψ : ℝ → H)
    (hu : ContDiffOn ℝ 1 u (I : Set ℝ)) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ I)
    (hpair : ∀ t, inner ℝ (deriv u t) (φ t) = inner ℝ (u t) (ψ t)) :
    Integrable (fun t => inner ℝ (u t) (deriv φ t + ψ t)) ∧
      (∫ t, inner ℝ (u t) (deriv φ t + ψ t)) = 0 := by
  simpa only [inner_add_right, hpair] using
    integral_inner_orbit_deriv_test_eq_zero I u φ hu hφ hc hs

end HeatKernel

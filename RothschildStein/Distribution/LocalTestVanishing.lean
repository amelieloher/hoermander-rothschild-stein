-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.AdjointTest
public import RothschildStein.Distribution.SmoothPartitionInfrastructure

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.Distribution

/-- local vanishing on real compact tests implies
vanishing of the whole distribution. A finite partition on each test
support gives the assertion without a global support restriction. -/
theorem distribution_eq_zero_of_local_test_vanishing {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (T : Distribution Ω ℂ (⊤ : ℕ∞))
    (hlocal : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ W : Set (Fin N → ℝ),
      IsOpen W ∧ x ∈ W ∧ ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport ψ ⊆ W → T ψ = 0) :
    T = 0 := by
  classical
  choose W hW hxW hzero using fun x : Ω => hlocal x x.property
  let U (x : Fin N → ℝ) := if hx : x ∈ (Ω : Set (Fin N → ℝ)) then W ⟨x, hx⟩ else univ
  ext ψ
  change T ψ = 0
  have hU : ∀ x ∈ tsupport ψ, U x ∈ nhds x := by
    intro x hx
    have hxΩ := ψ.tsupport_subset hx
    simpa only [U, dite_eq_left hxΩ] using (hW ⟨x, hxΩ⟩).mem_nhds (hxW ⟨x, hxΩ⟩)
  obtain ⟨ι, ρ, c, hρfin, hρsum, hρsmooth, hcK, hρsub⟩ :=
    exists_smooth_partition_on_compact (tsupport ψ) ψ.hasCompactSupport U hU
  have hfin := hρfin.finite_nonempty_inter_compact ψ.hasCompactSupport
  let s := hfin.toFinset
  let p (i : ι) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (hρsmooth i) ψ
  have hpcoe (i : ι) : (p i : (Fin N → ℝ) → ℝ) = fun x => ψ x * ρ i x := by
    simpa only [p, ContinuousLinearMap.mul_apply'] using
      TestFunction.bilinLeftCLM_apply (ContinuousLinearMap.mul ℝ ℝ) (hρsmooth i) ψ
  have hpapply (i : ι) (x : Fin N → ℝ) : p i x = ψ x * ρ i x := congrFun (hpcoe i) x
  have hp (i : ι) : T (p i) = 0 := by
    have hcΩ := ψ.tsupport_subset (hcK i)
    apply hzero ⟨c i, hcΩ⟩ (p i)
    have hsub := (tsupport_mul_subset_right (f := fun x => ψ x) (g := fun x => ρ i x)).trans (hρsub i)
    rw [hpcoe]
    simpa only [U, dite_eq_left hcΩ] using hsub
  have he : ∑ i ∈ s, p i = ψ := by
    ext x
    let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
      { toFun := fun φ => φ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    change ev (∑ i ∈ s, p i) = ψ x
    rw [map_sum]
    change (∑ i ∈ s, p i x) = ψ x
    simp_rw [hpapply]
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ tsupport ψ
    · have hsub : Function.support (fun i => ρ i x) ⊆ s := by
        intro i hi
        apply hfin.mem_toFinset.mpr
        exact ⟨x, hi, hx⟩
      rw [← finsum_eq_sum_of_support_subset _ hsub, hρsum x hx, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [← he, map_sum]
  simp only [hp, Finset.sum_const_zero]

end RothschildStein.Distribution

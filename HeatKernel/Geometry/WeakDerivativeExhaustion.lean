-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv
public import Mathlib.Topology.Compactness.Compact

/-! Consistent local weak derivatives patch along an increasing open exhaustion. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter TopologicalSpace
open scoped Topology
namespace HeatKernel

/-- Weak derivative representatives on an increasing open exhaustion determine a global
weak derivative, agreeing with every local representative almost everywhere. -/
theorem exists_global_weakWordDeriv_of_exhaustion {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin q))
    (U : ℕ → Opens (Fin N → ℝ))
    (hmono : ∀ {n m}, n ≤ m → (U n : Set (Fin N → ℝ)) ⊆ U m)
    (hcover : ∀ x : Fin N → ℝ, ∃ n, x ∈ (U n : Set (Fin N → ℝ)))
    {f : (Fin N → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (g : ℕ → (Fin N → ℝ) → ℝ)
    (hg : ∀ n, hasWeakWordDeriv X (U n) I f (g n)) :
    ∃ G : (Fin N → ℝ) → ℝ, hasWeakWordDeriv X ⊤ I f G ∧
      ∀ n, G =ᵐ[volume.restrict (U n : Set (Fin N → ℝ))] g n := by
  classical
  have hcons : ∀ n m, ∀ᵐ x ∂volume,
      x ∈ (U n : Set (Fin N → ℝ)) → x ∈ (U m : Set (Fin N → ℝ)) → g n x = g m x := by
    intro n m
    by_cases hnm : n ≤ m
    · have he := S.hasWeakWordDeriv_unique X (U n) (hg n)
        (S.hasWeakWordDeriv_restrict X (U m) (U n) (hmono hnm) (hg m))
      have he' := (ae_restrict_iff' (U n).isOpen.measurableSet).mp he
      exact he'.mono fun x hx hxn _ => hx hxn
    · have he := S.hasWeakWordDeriv_unique X (U m) (hg m)
        (S.hasWeakWordDeriv_restrict X (U n) (U m) (hmono (le_of_lt (lt_of_not_ge hnm))) (hg n))
      have he' := (ae_restrict_iff' (U m).isOpen.measurableSet).mp he
      exact he'.mono fun x hx _ hxm => (hx hxm).symm
  have hall : ∀ᵐ x ∂volume, ∀ n m,
      x ∈ (U n : Set (Fin N → ℝ)) → x ∈ (U m : Set (Fin N → ℝ)) → g n x = g m x :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (hcons n))
  let k := fun x => Nat.find (hcover x)
  let G := fun x => g (k x) x
  have heq : ∀ n, G =ᵐ[volume.restrict (U n : Set (Fin N → ℝ))] g n := by
    intro n
    have hallU := hall.filter_mono (ae_mono (Measure.restrict_le_self :
      volume.restrict (U n : Set (Fin N → ℝ)) ≤ volume))
    filter_upwards [hallU, ae_restrict_mem (U n).isOpen.measurableSet] with x hx hxn
    exact hx (k x) n (Nat.find_spec (hcover x)) hxn
  have hG : LocallyIntegrable G volume := by
    intro x
    obtain ⟨n, hn⟩ := hcover x
    have hlocal := (LocallyIntegrableOn.congr (heq n).symm (hg n).2.1) x hn
    simpa only [nhdsWithin_eq_nhds.mpr ((U n).isOpen.mem_nhds hn)] using hlocal
  refine ⟨G, ⟨hf.locallyIntegrableOn _, hG.locallyIntegrableOn _, ?_⟩, heq⟩
  intro φ
  obtain ⟨n, hn⟩ := φ.hasCompactSupport.elim_directed_cover
    (fun n => (U n : Set (Fin N → ℝ))) (fun n => (U n).isOpen)
    (fun x _ => by obtain ⟨n, hn⟩ := hcover x; exact mem_iUnion.mpr ⟨n, hn⟩)
    (fun n m => ⟨max n m, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
  let ψ : TestFunction (U n) ℝ (⊤ : ℕ∞) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hn⟩
  have hp := (hg n).2.2 ψ
  have he : (∫ x in (U n : Set (Fin N → ℝ)), G x * φ x) =
      ∫ x in (U n : Set (Fin N → ℝ)), g n x * φ x := by
    apply integral_congr_ae
    filter_upwards [heq n] with x hx
    rw [hx]
  change (∫ x in (⊤ : Opens (Fin N → ℝ)), G x * φ x) =
    ∫ x in (⊤ : Opens (Fin N → ℝ)), f x * wordTranspose X I φ x
  simp only [Opens.coe_top, Measure.restrict_univ]
  have hGzero : ∀ x, x ∉ (U n : Set (Fin N → ℝ)) → G x * φ x = 0 :=
    fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hn h)), mul_zero]
  have hfzero : ∀ x, x ∉ (U n : Set (Fin N → ℝ)) → f x * wordTranspose X I φ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hn (S.tsupport_wordTranspose_subset X I φ h))), mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hGzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hfzero, he]
  exact hp

end HeatKernel

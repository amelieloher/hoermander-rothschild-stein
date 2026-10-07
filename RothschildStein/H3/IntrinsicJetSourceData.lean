-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicSumSquaresTransfer
public import RothschildStein.H3.CompactSourceMass
public import RothschildStein.G2.MeasureConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- A finite sum preserves a common topological support bound. -/
theorem tsupport_finset_sum_subset {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → X → ℝ) {A : Set X}
    (hs : ∀ i ∈ s, tsupport (f i) ⊆ A) : tsupport (∑ i ∈ s, f i) ⊆ A := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
    intro hs
    rw [Finset.sum_insert hi]
    exact (tsupport_add _ _).trans (union_subset
      (hs i (Finset.mem_insert_self i s))
      (ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))))

/-- The actual intrinsic drift-plus-diagonal source is
continuous, compactly supported, and supported in the prescribed
common domain. No Euclidean differentiability of the input is used. -/
theorem intrinsicJetSource_data {N q : ℕ}
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hc : ∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I))
    (hs : ∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I))
    {A : Set (Fin N → ℝ)}
    (hA : ∀ I, wordWeight driftWeight I ≤ 2 → tsupport (jet I) ⊆ A) :
    let F := fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y
    Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ A := by
  classical
  have hw0 : wordWeight (driftWeight (q := q)) [0] ≤ 2 := by simp [wordWeight, driftWeight]
  have hw2 (i : Fin q) : wordWeight (driftWeight (q := q)) [i.succ, i.succ] ≤ 2 := by
    simp [wordWeight, driftWeight]
  have he : (jet [0] + ∑ i : Fin q, jet [i.succ, i.succ]) =
      (fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y) := by
    funext y
    simp only [Pi.add_apply, Finset.sum_apply]
  refine ⟨(hc [0] hw0).add (continuous_finsetSum _ (fun i _ => hc _ (hw2 i))), ?_, ?_⟩
  · rw [← he]
    exact (hs [0] hw0).add (HasCompactSupport.finset_sum (fun i _ => hs _ (hw2 i)))
  · rw [← he]
    exact (tsupport_add _ _).trans (union_subset (hA [0] hw0)
      (tsupport_finset_sum_subset Finset.univ (fun i : Fin q => jet [i.succ, i.succ])
        (fun i _ => hA _ (hw2 i))))

/-- The mass coefficient for an actual gauge support ball is
independent of its center, by the proved group measure identities. -/
theorem integral_abs_le_gaugeBall_mass {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) {ρ : ℝ} (hρ : 0 < ρ)
    {u : (Fin N → ℝ) → ℝ} (hu : Continuous u) (hsu : HasCompactSupport u)
    (z : Fin N → ℝ) (hs : tsupport u ⊆ G2.gaugeBall G ν z ρ) :
    (∫ y, |u y|) ≤ (volume (G2.gaugeBall G ν 0 ρ)).toReal * lpNorm u ∞ volume := by
  have hv : volume (G2.gaugeBall G ν z ρ) = volume (G2.gaugeBall G ν 0 ρ) := by
    rw [G2.volume_gaugeBall ν.gauge z hρ, G2.volume_gaugeBall ν.gauge 0 hρ]
  simpa only [hv] using integral_abs_le_support_volume_mul_lpNorm_top hu hsu
    (G2.isOpen_gaugeBall G ν.gauge z ρ).measurableSet
    (G2.volume_gaugeBall_ne_top G ν.gauge z ρ).lt_top hs

end RothschildStein.H3

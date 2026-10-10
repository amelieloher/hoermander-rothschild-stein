-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.LocalWeakDerivative
public import HeatKernel.Geometry.WeakDerivativeExhaustion

/-! Global bounded weak derivatives in constant horizontal directions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators
namespace HeatKernel

/-- A continuous horizontally Lipschitz function has a global weak derivative in every
constant horizontal direction, with the sharp directional bound. -/
theorem exists_bounded_weak_horizontal_derivative {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (b : Fin q → ℝ) (L : ℝ≥0) {f : (Fin N → ℝ) → ℝ}
    (hf : Continuous f)
    (hLip : ∀ x y, edist (f x) (f y) ≤ (L : ℝ≥0∞) * horizontalL2Distance (G.horizontalFields hq) x y) :
    ∃ g : (Fin N → ℝ) → ℝ,
      hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G (horizontalTangent hq b)) ⊤ [0] f g ∧
      ∀ᵐ x ∂volume, |g x| ≤ L * Real.sqrt (∑ i, b i ^ 2) := by
  let U : ℕ → Opens (Fin N → ℝ) := fun n => ⟨Metric.ball 0 ((n : ℝ) + 1), Metric.isOpen_ball⟩
  have hmono : ∀ {n m}, n ≤ m → (U n : Set (Fin N → ℝ)) ⊆ U m := by
    intro n m hnm x hx
    change dist x 0 < (n : ℝ) + 1 at hx
    change dist x 0 < (m : ℝ) + 1
    exact hx.trans_le (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hcover : ∀ x : Fin N → ℝ, ∃ n, x ∈ (U n : Set (Fin N → ℝ)) := by
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (dist x 0)
    exact ⟨n, by change dist x 0 < (n : ℝ) + 1; linarith⟩
  have hfinite : ∀ n, volume (U n : Set (Fin N → ℝ)) ≠ ⊤ := by
    intro n
    have hm : volume (U n : Set (Fin N → ℝ)) ≤ volume (Metric.closedBall (0 : Fin N → ℝ) ((n : ℝ) + 1)) :=
      measure_mono Metric.ball_subset_closedBall
    exact ne_of_lt (hm.trans_lt (isCompact_closedBall (0 : Fin N → ℝ) ((n : ℝ) + 1)).measure_lt_top)
  choose g hg hb using fun n => exists_bounded_local_weak_horizontal_derivative G hq b L hf hLip (U n) (hfinite n)
  obtain ⟨D, hD, heq⟩ := exists_global_weakWordDeriv_of_exhaustion
    (fun _ : Fin 1 => G2.leftField G (horizontalTangent hq b)) [0] U hmono hcover
    hf.locallyIntegrable g hg
  refine ⟨D, hD, ?_⟩
  have hbound : ∀ n, ∀ᵐ x ∂volume.restrict (U n : Set (Fin N → ℝ)),
      |D x| ≤ L * Real.sqrt (∑ i, b i ^ 2) := by
    intro n
    filter_upwards [heq n, hb n] with x hx hbx
    rw [hx]
    exact hbx
  have hUnion : (⋃ n, (U n : Set (Fin N → ℝ))) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := hcover x
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hall := (ae_restrict_iUnion_iff (fun n => (U n : Set (Fin N → ℝ))) _).mpr hbound
  simpa only [hUnion, Measure.restrict_univ] using hall

end HeatKernel

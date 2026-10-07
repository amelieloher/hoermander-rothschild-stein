-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.TruncatedDistanceComparison
public import RothschildStein.S.DistanceGeometry
public import RothschildStein.S.WeakKernelTransferPatch
public import RothschildStein.G1.LocalDistanceLower

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- The weighted control distance has a Euclidean-linear comparison on each interior relatively compact patch, by the first-exit lower bound for controlled curves (BB Proposition 1.42, pp. 23–24; Theorem 1.53, (1.45), p. 35). -/
theorem exists_controlDistance_comparison_on_compact_patch
    (Ω : Opens (Fin n → ℝ)) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hw : ∀ i,(w i : ℕ) ≤ 2)
    (hX : ∀ i,ContinuousOn (X i) (Ω : Set (Fin n → ℝ)))
    {V : Set (Fin n → ℝ)} (hc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ κ : ℝ,DistanceComparison (controlDistance (Ω : Set (Fin n → ℝ)) w X) V κ := by
  obtain ⟨δ,hδ,hδΩ⟩ := exists_friedrichs_interior_radius Ω hc hVΩ
  have hct : ContinuousOn (fun z => ∑ i : Fin q,‖X i z‖) (cthickening δ (closure V)) :=
    continuousOn_finsetSum Finset.univ (fun i _ => ((hX i).mono hδΩ).norm)
  obtain ⟨M,hM⟩ := (hc.cthickening.image_of_continuousOn hct).bddAbove
  let B := max M 1
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right M 1)
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuousOn (continuous_id : Continuous (fun x : Fin n → ℝ => x)).continuousOn
  simp only [id_eq] at hA
  let D := max (2*A) 0
  have hD : 0 ≤ D := le_max_right _ _
  let ρ := min 1 (δ/B)
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hδ hB)
  obtain ⟨κ,hκ,hconst⟩ := exists_truncated_distance_comparison_constant hB hρ hD
  refine ⟨κ,hκ,?_⟩
  intro x hx y hy
  have hbound : ∀ z,‖z-x‖ ≤ δ → ∑ i : Fin q,‖X i z‖ ≤ B := by
    intro z hz
    have ht : z ∈ cthickening δ (closure V) :=
      mem_cthickening_of_dist_le z x δ (closure V) (subset_closure hx) (by simpa only [dist_eq_norm] using hz)
    exact (hM ⟨z,ht,rfl⟩).trans (le_max_left _ _)
  have hdiam : ‖y-x‖ ≤ D := by
    exact (norm_sub_le y x).trans ((show ‖y‖+‖x‖ ≤ 2*A from by
      linarith [hA y (subset_closure hy),hA x (subset_closure hx)]).trans (le_max_left _ _))
  have hlower := G1.controlDistance_lower_bound_of_buffer (Ω := (Ω : Set (Fin n → ℝ))) hw x y hB hδ hbound
  have hn := hconst ‖y-x‖ (norm_nonneg _) hdiam
  have hmin : min 1 (min (δ/B) (‖y-x‖/B)) = min ρ (‖y-x‖/B) := by
    dsimp only [ρ]
    rw [min_assoc]
  rw [hmin] at hlower
  calc
    ENNReal.ofReal ‖x-y‖ = ENNReal.ofReal ‖y-x‖ := by rw [norm_sub_rev]
    _ ≤ ENNReal.ofReal (κ*min ρ (‖y-x‖/B)) := ENNReal.ofReal_le_ofReal hn
    _ = ENNReal.ofReal κ*ENNReal.ofReal (min ρ (‖y-x‖/B)) := ENNReal.ofReal_mul hκ.le
    _ ≤ ENNReal.ofReal κ*controlDistance (Ω : Set (Fin n → ℝ)) w X x y :=
      mul_le_mul_right hlower _

end RothschildStein.S

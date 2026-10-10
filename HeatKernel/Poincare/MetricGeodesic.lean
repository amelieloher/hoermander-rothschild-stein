-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! Minimizing metric paths from arbitrarily close constant-speed competitors. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace HeatKernel

/-- In a proper metric space, arbitrarily close constant-speed competitors yield a path
with the optimal Lipschitz constant. Compactness of the product of one containing ball
preserves all pointwise distance inequalities. -/
theorem exists_optimal_metric_path_of_approximate_paths {E : Type*} [MetricSpace E]
    [ProperSpace E] (x y : E)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ γ : Icc (0 : ℝ) 1 → E,
        γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (γ s) (γ t) ≤ (dist x y + ε) * dist s t) :
    ∃ γ : Icc (0 : ℝ) 1 → E,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (γ s) (γ t) ≤ dist x y * dist s t := by
  let z : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let o : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  let K : Set (Icc (0 : ℝ) 1 → E) := pi univ (fun _ => closedBall x (dist x y + 1))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall x (dist x y + 1)
  let A : {ε : ℝ // 0 < ε} → Set (Icc (0 : ℝ) 1 → E) := fun ε =>
    K ∩ {γ | γ z = x ∧ γ o = y ∧
      ∀ s t, dist (γ s) (γ t) ≤ (dist x y + ε) * dist s t}
  have hclosed : ∀ ε, IsClosed (A ε) := by
    intro ε
    apply hK.isClosed.inter
    apply (isClosed_eq (continuous_apply z) continuous_const).inter
    apply (isClosed_eq (continuous_apply o) continuous_const).inter
    change IsClosed {γ : Icc (0 : ℝ) 1 → E |
      ∀ s t, dist (γ s) (γ t) ≤ (dist x y + (ε : ℝ)) * dist s t}
    simp only [ofPred_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun t =>
      isClosed_le ((continuous_apply s : Continuous (fun γ : Icc (0 : ℝ) 1 → E => γ s)).dist
        (continuous_apply t))
        (continuous_const : Continuous (fun _ : Icc (0 : ℝ) 1 → E =>
          (dist x y + (ε : ℝ)) * dist s t))
  have hnonempty : ∀ ε, (A ε).Nonempty := by
    intro ε
    obtain ⟨γ, hz, ho, hγ⟩ := happrox (min ε 1) (lt_min ε.2 zero_lt_one)
    refine ⟨γ, ?_, hz, ho, fun s t => (hγ s t).trans ?_⟩
    · intro t _
      change dist (γ t) x ≤ dist x y + 1
      have ht : dist t z ≤ 1 := by
        change |(t : ℝ) - 0| ≤ 1
        simpa only [sub_zero, abs_of_nonneg t.2.1] using t.2.2
      have hb := hγ t z
      rw [hz] at hb
      apply hb.trans
      calc
        (dist x y + min (ε : ℝ) 1) * dist t z ≤ (dist x y + 1) * dist t z :=
          mul_le_mul_of_nonneg_right (add_le_add_right (min_le_right _ _) _) dist_nonneg
        _ ≤ dist x y + 1 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left ht
            (by positivity : 0 ≤ dist x y + 1)
    · exact mul_le_mul_of_nonneg_right (add_le_add_right (min_le_left _ _) _) dist_nonneg
  have hdir : Directed (· ⊇ ·) A := by
    intro ε δ
    refine ⟨⟨min ε δ, lt_min ε.2 δ.2⟩, ?_, ?_⟩
    · rintro γ ⟨hγK, hz, ho, hγ⟩
      exact ⟨hγK, hz, ho, fun s t => (hγ s t).trans
        (mul_le_mul_of_nonneg_right (add_le_add_right (min_le_left _ _) _) dist_nonneg)⟩
    · rintro γ ⟨hγK, hz, ho, hγ⟩
      exact ⟨hγK, hz, ho, fun s t => (hγ s t).trans
        (mul_le_mul_of_nonneg_right (add_le_add_right (min_le_right _ _) _) dist_nonneg)⟩
  have : Nonempty {ε : ℝ // 0 < ε} := ⟨⟨1, zero_lt_one⟩⟩
  obtain ⟨γ, hγ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed A hdir
    hnonempty (fun ε => hK.of_isClosed_subset (hclosed ε) inter_subset_left) hclosed
  have hh := mem_iInter.mp hγ
  refine ⟨γ, (hh ⟨1, zero_lt_one⟩).2.1, (hh ⟨1, zero_lt_one⟩).2.2.1, ?_⟩
  intro s t
  by_contra hn
  have hgap : 0 < dist (γ s) (γ t) - dist x y * dist s t := sub_pos.mpr (lt_of_not_ge hn)
  let ε := (dist (γ s) (γ t) - dist x y * dist s t) / (dist s t + 1)
  have hε : 0 < ε := div_pos hgap (by positivity)
  have hb := (hh ⟨ε, hε⟩).2.2.2 s t
  have he : ε * (dist s t + 1) = dist (γ s) (γ t) - dist x y * dist s t :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

end HeatKernel

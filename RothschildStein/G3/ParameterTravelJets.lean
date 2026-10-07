-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ChronologicalJetBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A preserved parameter and a spatial travel budget control all jet inputs. -/
theorem chronologicalJetBounds_of_parameter_travel (q : ℕ) (B : ℝ)
    (fs : List (P × E → P × E)) (t : P) (x y : E) {ρ d : ℝ} (hd : 0 ≤ d)
    (hs : ∀ f ∈ fs, ∀ z ∈ ball x ρ, ContDiffAt ℝ q f (t,z))
    (hj : ∀ f ∈ fs, ∀ z ∈ ball x ρ, ∀ k, 1 ≤ k → k ≤ q →
      ‖iteratedFDeriv ℝ k f (t,z)‖ ≤ B)
    (hp : ∀ f ∈ fs, ∀ z, (f (t,z)).1 = t)
    (ht : ∀ f ∈ fs, ∀ z ∈ ball x ρ, ‖(f (t,z)).2-z‖ ≤ d)
    (hb : ‖y-x‖ + fs.length*d < ρ) : ChronologicalJetBounds q B fs (t,y) := by
  induction fs generalizing y with
  | nil => trivial
  | cons f fs ih =>
    have hy : y ∈ ball x ρ := by
      rw [mem_ball,dist_eq_norm]
      have hn : 0 ≤ (fs.length+1 : ℝ)*d := mul_nonneg (by positivity) hd
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hb
      linarith
    refine ⟨hs f List.mem_cons_self y hy,
      fun k hk hkq => hj f List.mem_cons_self y hy k hk hkq,?_⟩
    have hnext := ih (f (t,y)).2
      (fun g hg => hs g (List.mem_cons_of_mem f hg))
      (fun g hg => hj g (List.mem_cons_of_mem f hg))
      (fun g hg => hp g (List.mem_cons_of_mem f hg))
      (fun g hg => ht g (List.mem_cons_of_mem f hg))
    have he := (norm_sub_le_norm_sub_add_norm_sub (f (t,y)).2 y x).trans
      (add_le_add (ht f List.mem_cons_self y hy) (le_refl ‖y-x‖))
    have hbudget : ‖(f (t,y)).2-x‖ + fs.length*d < ρ := by
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hb
      nlinarith
    have hpair : f (t,y) = (t,(f (t,y)).2) := by
      exact Prod.ext (hp f List.mem_cons_self y) rfl
    rw [hpair]
    exact hnext hbudget
end RothschildStein.G3

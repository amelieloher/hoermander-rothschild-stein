-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TimedPrimitiveSchedules
public import Mathlib.Analysis.Normed.Group.Basic
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

def TimedScheduleInside {a : ℕ} {E : Type*} (Φ : Fin a → E × ℝ → E)
    (Ω : Set E) : List (Fin a × ℝ) → E → Prop
  | [], _ => True
  | b :: S, x => (∀ θ ∈ Icc (0 : ℝ) 1, Φ b.1 (x,θ*b.2) ∈ Ω) ∧
      TimedScheduleInside Φ Ω S (Φ b.1 (x,b.2))

theorem timedScheduleInside_mono {a : ℕ} {E : Type*}
    (Φ : Fin a → E × ℝ → E) {Ω V : Set E} (hsub : Ω ⊆ V)
    (S : List (Fin a × ℝ)) (x : E) (h : TimedScheduleInside Φ Ω S x) :
    TimedScheduleInside Φ V S x := by
  induction S generalizing x with
  | nil => trivial
  | cons b S ih => exact ⟨fun θ hθ => hsub (h.1 θ hθ),ih _ h.2⟩

/-- A numerical total displacement budget controls every continuous arc. -/
theorem timedSchedule_inside_ball_of_budget {a : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : Fin a → E × ℝ → E) (x₀ : E) {R τ B T : ℝ}
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hTτ : T < τ)
    (hflow : ∀ i y, y ∈ ball x₀ R → ∀ t : ℝ, |t| < τ →
      ‖Φ i (y,t)-y‖ ≤ B*|t|)
    (S : List (Fin a × ℝ)) (x : E)
    (htime : ∀ Z ∈ S, |Z.2| ≤ T)
    (hbudget : ‖x-x₀‖+(S.length : ℝ)*(B*T) < R) :
    TimedScheduleInside Φ (ball x₀ R) S x ∧
      ‖runTimedPrimitiveSchedule Φ S x-x₀‖ ≤ ‖x-x₀‖+(S.length : ℝ)*(B*T) := by
  induction S generalizing x with
  | nil => exact ⟨trivial,by simp [runTimedPrimitiveSchedule]⟩
  | cons b S ih =>
    have hb := htime b (List.mem_cons_self ..)
    have hx : x ∈ ball x₀ R := by
      rw [mem_ball,dist_eq_norm]
      have hnon : 0 ≤ ((b::S).length : ℝ)*(B*T) := by positivity
      linarith
    have hend : ‖Φ b.1 (x,b.2)-x‖ ≤ B*T :=
      (hflow b.1 x hx b.2 (hb.trans_lt hTτ)).trans (mul_le_mul_of_nonneg_left hb hB)
    have hnew : ‖Φ b.1 (x,b.2)-x₀‖ ≤ ‖x-x₀‖+B*T := by
      exact (norm_sub_le_norm_sub_add_norm_sub _ x _).trans (by linarith)
    have hlen : ((b::S).length : ℝ) = (S.length : ℝ)+1 := by simp
    have hbudget' : ‖Φ b.1 (x,b.2)-x₀‖+(S.length : ℝ)*(B*T) < R := by
      rw [hlen] at hbudget
      nlinarith
    obtain ⟨hinside,hendall⟩ := ih (Φ b.1 (x,b.2))
      (fun Z hZ => htime Z (List.mem_cons_of_mem b hZ)) hbudget'
    refine ⟨⟨?_,hinside⟩,?_⟩
    · intro θ hθ
      have hθtime : |θ*b.2| ≤ T := by
        rw [abs_mul,abs_of_nonneg hθ.1]
        exact (mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg b.2)).trans (by simpa using hb)
      have hdisp := (hflow b.1 x hx (θ*b.2) (hθtime.trans_lt hTτ)).trans
        (mul_le_mul_of_nonneg_left hθtime hB)
      rw [mem_ball,dist_eq_norm]
      have htri := norm_sub_le_norm_sub_add_norm_sub (Φ b.1 (x,θ*b.2)) x x₀
      have hn : 0 ≤ (S.length : ℝ)*(B*T) := by positivity
      rw [hlen] at hbudget
      nlinarith
    · change ‖runTimedPrimitiveSchedule Φ S (Φ b.1 (x,b.2))-x₀‖ ≤ _
      rw [hlen]
      nlinarith
end RothschildStein.G3

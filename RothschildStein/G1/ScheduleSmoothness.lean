-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CommutatorSchedule
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

variable {ι P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint smoothness is needed only at the points of the finite
trajectory (BB Lemma 1.52, pp. 30–31). -/
def ScheduleSmoothAt (A : ι × Bool → P × E → E) (p : P) :
    List (ι × Bool) → E → Prop
  | [], _ => True
  | a :: S, x => ContDiffAt ℝ (⊤ : ℕ∞) (A a) (p, x) ∧
      ScheduleSmoothAt A p S (A a (p, x))

/-- Finite composition preserves joint smoothness in the independent
parameters and initial point, using local hypotheses at actual arc endpoints
(BB Lemma 1.52, pp. 30–31). -/
theorem runSchedule_contDiffAt_of_arc_smoothness
    (A : ι × Bool → P × E → E) (p : P) (S : List (ι × Bool)) (x : E)
    (h : ScheduleSmoothAt A p S x) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : P × E => runSchedule (fun a y => A a (q.1, y)) S q.2) (p, x) := by
  induction S generalizing x with
  | nil => exact contDiffAt_snd
  | cons a S ih =>
    change ContDiffAt ℝ (⊤ : ℕ∞)
      ((fun q : P × E => runSchedule (fun b y => A b (q.1, y)) S q.2) ∘
        (fun q : P × E => (q.1, A a q))) (p, x)
    exact (ih (A a (p, x)) h.2).comp (p, x) (contDiffAt_fst.prodMk h.1)

end RothschildStein.G1

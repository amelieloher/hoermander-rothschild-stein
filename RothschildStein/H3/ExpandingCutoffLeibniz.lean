-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExpandingCutoffProducts
public import RothschildStein.H3.ExpandingCutoffSource
public import RothschildStein.H3.PlateauWords
public import RothschildStein.S.MultiplicationBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- The complete ordered Leibniz expression for an expanding cutoff
converges in Lp to the expression for the constant multiplier one. -/
theorem tendsto_expandingCutoff_leibniz_eLpNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (I : List (Fin (q+1)))
    (F : List (Fin (q+1)) → (Fin N → ℝ) → ℝ)
    {p : ℝ} (hp : 1 ≤ p)
    (hF : ∀ J, J.Sublist I → MemLp (F J) (ENNReal.ofReal p) volume) :
    Tendsto (fun R : ℝ => eLpNorm
      (fun x => S.leibnizWordValue H.fields I F
          (smoothQuasiballCutoff G ν 0 R (2*R)) x -
        S.leibnizWordValue H.fields I F (fun _ => 1) x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  classical
  let E := fun R (a : List (Fin (q+1)) × List (Fin (q+1))) x =>
    F a.1 x * wordDerivative H.fields a.2 (smoothQuasiballCutoff G ν 0 R (2*R)) x -
    F a.1 x * wordDerivative H.fields a.2 (fun _ => 1) x
  have hterm : ∀ a ∈ S.leibnizSplits I,
      Tendsto (fun R => eLpNorm (E R a) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    intro a ha
    have hf := hF a.1 (S.leibnizSplits_sublist I a ha).1
    by_cases hz : a.2 = []
    · simpa only [E, hz, wordDerivative, mul_one] using
        tendsto_expandingCutoff_mul_eLpNorm G ν hν (by linarith) hf
    · have he : wordDerivative H.fields a.2 (fun _ => (1 : ℝ)) = fun _ => 0 := by
        simpa only [hz, ite_false] using wordDerivative_const H.fields a.2 (1 : ℝ)
      simpa only [E, he, mul_zero, sub_zero] using
        tendsto_expandingCutoff_word_mul_eLpNorm G H ν hν a.2 hz 0 volume hf
  have hsum : ∀ l : List (List (Fin (q+1)) × List (Fin (q+1))),
      (∀ a ∈ l, a ∈ S.leibnizSplits I) →
      Tendsto (fun R => (l.map (fun a => eLpNorm (E R a) (ENNReal.ofReal p) volume)).sum)
        atTop (𝓝 0) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro hl
      simpa only [List.map_cons, List.sum_cons, add_zero] using
        (hterm a (hl a (by simp))).add (ih (fun b hb => hl b (by simp [hb])))
  have hb (R : ℝ) := S.eLpNorm_list_sum_le (S.leibnizSplits I) (E R)
    (ENNReal.ofReal p) (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp) volume
  have he (R : ℝ) : (fun x => S.leibnizWordValue H.fields I F
      (smoothQuasiballCutoff G ν 0 R (2*R)) x -
      S.leibnizWordValue H.fields I F (fun _ => 1) x) =
      (fun x => ((S.leibnizSplits I).map (fun a => E R a x)).sum) := by
    funext x
    unfold S.leibnizWordValue
    have hs (l : List (List (Fin (q+1)) × List (Fin (q+1)))) :
        (l.map (fun a => F a.1 x * wordDerivative H.fields a.2
          (smoothQuasiballCutoff G ν 0 R (2*R)) x)).sum -
        (l.map (fun a => F a.1 x * wordDerivative H.fields a.2 (fun _ => 1) x)).sum =
        (l.map (fun a => E R a x)).sum := by
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [show ∀ A B C D : ℝ, (A+B)-(C+D)=(A-C)+(B-D) by intros; ring, ih]
    exact hs _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hsum _ (fun _ h => h)) (fun _ => bot_le) (fun R => by rw [he R]; exact hb R)

end RothschildStein.H3

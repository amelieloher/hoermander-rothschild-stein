-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ScalarIntegration

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter

namespace RothschildStein.L1

/-- Successive scalar integration constructs a triangular
system on the entire interval, provided each determined right side is
integrable. This hypothesis is discharged by bounded measurable controls
and continuous polynomial coefficients. -/
theorem exists_triangular_ac_solution_of_integrable_on_interval {m : ℕ} {a b : ℝ}
    (F : Fin m → ℝ → (Fin m → ℝ) → ℝ)
    (hF : ∀ l t v u, t ∈ uIcc a b → (∀ j : Fin m, j.val < l.val → v j = u j) →
      F l t v = F l t u)
    (hInt : ∀ l (v : ℝ → (Fin m → ℝ)),
      (∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) a b) →
      IntervalIntegrable (fun t => F l t (v t)) volume a b)
    (z : Fin m → ℝ) :
    ∃ v : ℝ → (Fin m → ℝ),
      (∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) a b) ∧ v a = z ∧
      ∀ l, ∀ᵐ t ∂volume, t ∈ uIcc a b →
        HasDerivAt (fun t => v t l) (F l t (v t)) t := by
  classical
  have hstep : ∀ k : ℕ, k ≤ m → ∃ v : ℝ → (Fin m → ℝ),
      (∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) a b) ∧ v a = z ∧
      ∀ l : Fin m, l.val < k → ∀ᵐ t ∂volume, t ∈ uIcc a b →
        HasDerivAt (fun t => v t l) (F l t (v t)) t := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ => z, ?_, rfl, ?_⟩
      · intro j
        simpa only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero] using
          (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ)) _ (nhds 0))
      · intro l hl
        omega
    | succ k ih =>
      intro hkm
      obtain ⟨v, hv, hvz, hvd⟩ := ih (by omega)
      let l : Fin m := ⟨k, by omega⟩
      obtain ⟨p, hp, hpz, hpd⟩ := exists_scalar_ac_primitive (hInt l v hv) (z l)
      let u : ℝ → (Fin m → ℝ) := fun t j => if j = l then p t else v t j
      have heq : ∀ j : Fin m, j.val < k → ∀ t, u t j = v t j := by
        intro j hj t
        have hne : j ≠ l := by intro h; subst j; simp [l] at hj
        simp only [u, hne, ite_false]
      have hFu : ∀ j : Fin m, j.val ≤ k → ∀ t ∈ uIcc a b, F j t (u t) = F j t (v t) := by
        intro j hj t ht
        apply hF j t _ _ ht
        intro i hi
        exact heq i (by omega) t
      refine ⟨u, ?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = l
        · subst j
          simpa only [u, ite_true] using hp
        · simpa only [u, hj, ite_false] using hv j
      · funext j
        by_cases hj : j = l
        · subst j
          simpa only [u, ite_true] using hpz
        · simpa only [u, hj, ite_false] using congrFun hvz j
      · intro j hj
        by_cases hlast : j = l
        · subst j
          filter_upwards [hpd] with t ht
          intro hmem
          rw [hFu l (by simp [l]) t hmem]
          simpa only [u, ite_true] using ht hmem
        · have hjk : j.val < k := by
            have hneval : j.val ≠ k := fun he => hlast (Fin.ext he)
            omega
          filter_upwards [hvd j hjk] with t ht
          intro hmem
          have hder := ht hmem
          rw [hFu j hjk.le t hmem]
          simpa only [u, hlast, ite_false] using hder
  obtain ⟨v, hv, hvz, hvd⟩ := hstep m le_rfl
  exact ⟨v, hv, hvz, fun l => hvd l l.isLt⟩

/-- The unrestricted dependency hypothesis is a specialization
of the interval-local integration theorem. -/
theorem exists_triangular_ac_solution_of_integrable {m : ℕ} {a b : ℝ}
    (F : Fin m → ℝ → (Fin m → ℝ) → ℝ)
    (hF : ∀ l t v u, (∀ j : Fin m, j.val < l.val → v j = u j) →
      F l t v = F l t u)
    (hInt : ∀ l (v : ℝ → (Fin m → ℝ)),
      (∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) a b) →
      IntervalIntegrable (fun t => F l t (v t)) volume a b)
    (z : Fin m → ℝ) :
    ∃ v : ℝ → (Fin m → ℝ),
      (∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) a b) ∧ v a = z ∧
      ∀ l, ∀ᵐ t ∂volume, t ∈ uIcc a b →
        HasDerivAt (fun t => v t l) (F l t (v t)) t := by
  exact exists_triangular_ac_solution_of_integrable_on_interval F
    (fun l t v u _ => hF l t v u) hInt z

end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ReductionValue
public import RothschildStein.G4.PiJetBounds
public import RothschildStein.G4.CompositionJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Uniform finite jets of the determinant polynomial on a
universal field-value ball, independently of the actual spatial fields. -/
theorem exists_valueFrameDet_jet_bound (n h : ℕ) (P : ℝ) :
    ∃ C : ℝ, 0 < C ∧ HasJetBound (univ : Set (ReductionValues n n))
      (Metric.closedBall 0 P) (valueFrameDet (fun i : Fin n => i)) h C := by
  classical
  let f := valueFrameDet (fun i : Fin n => i)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := valueFrameDet_contDiff _
  have hex : ∀ j : Fin (h + 1), ∃ C : ℝ, ∀ u ∈ Metric.closedBall 0 P,
      ‖iteratedFDerivWithin ℝ j.val f univ u‖ ≤ C := by
    intro j
    have hc := hf.contDiffOn.continuousOn_iteratedFDerivWithin
      (m := j.val) (by simp) uniqueDiffOn_univ
    obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ReductionValues n n) P).image_of_continuousOn
      (hc.mono (subset_univ _))).isBounded.exists_norm_le
    exact ⟨C, fun u hu => hC _ (mem_image_of_mem _ hu)⟩
  choose C hC using hex
  let D := 1 + ∑ j : Fin (h + 1), |C j|
  have hn : 0 ≤ ∑ j : Fin (h + 1), |C j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro j hj u hu
  let j' : Fin (h + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have he := Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ j')
  have hb := (hC j' u hu).trans (le_abs_self (C j'))
  exact hb.trans (by dsimp [D]; linarith)

/-- Every actual frame determinant has a universal finite-jet
budget from the common field-jet budget. No nondegeneracy is needed. -/
theorem exists_frameDet_jet_bound (n h : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω) →
      (∀ i, HasJetBound Ω K (Z i) h P) → ∀ B : Fin n → ι,
      HasJetBound Ω K (frameDet Z B) h C := by
  obtain ⟨A, hA, hAj⟩ := exists_valueFrameDet_jet_bound n h P
  let C := compositionJetBudget h A P
  have hC : 0 < C := by
    unfold C compositionJetBudget
    have he := Finset.single_le_sum (f := fun j => (j.factorial : ℝ) * A * (1 + P) ^ j)
      (fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA.le) (pow_nonneg (by linarith) _))
      (Finset.mem_range.mpr (Nat.zero_lt_succ h))
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one] at he
    exact hA.trans_le he
  refine ⟨C, hC, ?_⟩
  intro ι Ω K hΩ hKΩ Z hZ hjets B
  let g : (Fin n → ℝ) → ReductionValues n n :=
    fun x => Sum.elim (fun i => Z (B i) x) (fun _ => 0)
  have hgs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => g x i) Ω := by
    intro i
    cases i with
    | inl i => exact hZ (B i)
    | inr i => exact contDiffOn_const
  have hgj : ∀ i, HasJetBound Ω K (fun x => g x i) h P := by
    intro i
    cases i with
    | inl i => exact hjets (B i)
    | inr i =>
      intro j hj x hx
      cases j with
      | zero => simpa [g] using hP
      | succ j => simpa [g, iteratedFDerivWithin_succ_const] using hP
  have hgjoint := HasJetBound.pi hΩ hKΩ hgs hP hgj
  have hm : MapsTo g K (Metric.closedBall 0 P) := by
    intro x hx
    have he : ‖g x‖ ≤ P := by simpa using hgjoint 0 (Nat.zero_le _) x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using he
  have hb := hgjoint.comp hΩ isOpen_univ hKΩ (contDiffOn_pi.mpr hgs)
    (valueFrameDet_contDiff (fun i : Fin n => i)).contDiffOn (mapsTo_univ _ _) hm hP hA.le hAj
  change HasJetBound Ω K ((valueFrameDet (fun i : Fin n => i)) ∘ g) h C
  exact hb

end RothschildStein.G4

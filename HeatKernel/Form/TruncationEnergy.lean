-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.PositivePart

/-! # Mixed energy identities for truncations -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Restricting the gradient makes the mixed energy equal the truncated energy. -/
theorem horizontalEnergy_eq_of_gradient_restriction {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u v : energyGraph U X)
    (P : (Fin N → ℝ) → Prop) [DecidablePred P]
    (hv : ∀ i, (v : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => if P x then (u : GradientSpace U q).snd i x else 0) :
    horizontalEnergy U X u v = horizontalEnergy U X v v := by
  simp only [horizontalEnergy, energyGradient_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv i] with x hx
  rw [hx]
  by_cases h : P x
  · rw [ite_eq_left h]
  · simp only [ite_eq_right h, inner_zero_right]

/-- Restricting the negative gradient gives the negative of the truncated energy. -/
theorem horizontalEnergy_eq_neg_of_gradient_restriction {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u v : energyGraph U X)
    (P : (Fin N → ℝ) → Prop) [DecidablePred P]
    (hv : ∀ i, (v : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => if P x then -(u : GradientSpace U q).snd i x else 0) :
    horizontalEnergy U X u v = -horizontalEnergy U X v v := by
  simp only [horizontalEnergy, energyGradient_apply, PiLp.inner_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hv i] with x hx
  rw [hx]
  by_cases h : P x
  · simp only [ite_eq_left h, inner_neg_right, inner_neg_left, neg_neg]
  · simp only [ite_eq_right h, inner_zero_right, neg_zero]

/-- Positive-level truncations satisfy the mixed energy identity. -/
theorem exists_energyGraph_positiveLevel_energy_eq {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (v : energyGraph (N := N) ⊤ X)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => max ((v : GradientSpace (N := N) ⊤ q).fst x - c) 0) ∧
      horizontalEnergy ⊤ X v z = horizontalEnergy ⊤ X z z := by
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_positiveLevel X hX v c hc
  refine ⟨z, hzf, ?_⟩
  apply horizontalEnergy_eq_of_gradient_restriction ⊤ X v z
    (fun x => c < (v : GradientSpace (N := N) ⊤ q).fst x)
  simpa only [Opens.coe_top, Measure.restrict_univ] using hzg

/-- Negative parts satisfy the negative mixed energy identity. -/
theorem exists_energyGraph_negativePart_energy_eq {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (v : energyGraph (N := N) ⊤ X) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => max (-(v : GradientSpace (N := N) ⊤ q).fst x) 0) ∧
      horizontalEnergy ⊤ X v z = -horizontalEnergy ⊤ X z z := by
  let U : Opens (Fin N → ℝ) := ⊤
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_positivePart X hX (-v)
  simp only [Submodule.coe_neg, WithLp.neg_fst, WithLp.neg_snd, PiLp.neg_apply] at hzf hzg
  have hneg : (-(v : GradientSpace U q).fst : SpatialL2 U) =ᵐ[volume]
      fun x => -(v : GradientSpace U q).fst x := by
    simpa only [U, Opens.coe_top, Measure.restrict_univ, Pi.neg_def] using
      Lp.coeFn_neg (v : GradientSpace U q).fst
  refine ⟨z, hzf.trans (hneg.fun_comp (fun s : ℝ => max s 0)), ?_⟩
  apply horizontalEnergy_eq_neg_of_gradient_restriction U X v z
    (fun x => (v : GradientSpace U q).fst x < 0)
  intro i
  have H : (z : GradientSpace U q).snd i =ᵐ[volume]
      fun x => if (v : GradientSpace U q).fst x < 0 then -(v : GradientSpace U q).snd i x else 0 := by
    have hgneg : (-(v : GradientSpace U q).snd i : SpatialL2 U) =ᵐ[volume]
        fun x => -(v : GradientSpace U q).snd i x := by
      simpa only [U, Opens.coe_top, Measure.restrict_univ, Pi.neg_def] using
        Lp.coeFn_neg ((v : GradientSpace U q).snd i)
    filter_upwards [hzg i, hneg, hgneg] with x hx hnx hgnx
    simpa only [hnx, hgnx, neg_pos] using hx
  simpa only [U, Opens.coe_top, Measure.restrict_univ] using H

end HeatKernel

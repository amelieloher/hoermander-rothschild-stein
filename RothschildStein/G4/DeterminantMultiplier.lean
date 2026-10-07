-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortGeneratorDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Divergence is smooth on an open smoothness domain
(BB Lemma 9.37, pp. 428–430). -/
theorem divergence_contDiffOn {n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {T : (Fin n → ℝ) → (Fin n → ℝ)} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Hormander.Interface.euclideanDivergence T) Ω := by
  apply ContDiffOn.sum
  intro j hj
  exact contDiffOn_pi.mp ((hT.fderiv_of_isOpen hΩ (by simp)).clm_apply
    (contDiffOn_const (c := Hormander.Interface.basisVec j))) j

/-- The first relative determinant derivative, expressed before
iterating the generator calculus (BB Lemma 9.37, pp. 428–430). -/
def determinantMultiplier {k n s : ℕ} (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ShortWord w s) (L : ShortWord w s) (x : Fin n → ℝ) : ℝ :=
  Hormander.Interface.euclideanDivergence (shortField w X L) x +
    ∑ j, ∑ K, shortBracketCoefficient w X L (B j) K x *
      frameCoefficient (shortField w X) B (shortField w X K) j x

/-- The multiplier has one generator factor and deficit minus
its field's weight (BB Lemma 9.37, pp. 428–430). -/
theorem determinantMultiplier_expansion {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s) (L : ShortWord w s) :
    HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B 1
      (-((shortWeight w L : ℕ) : ℤ)) (determinantMultiplier w X B L) := by
  classical
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  have hneg : -((v L : ℕ) : ℤ) ≤ 0 := neg_nonpos.mpr (by positivity)
  have hd := HasGeneratorExpansion.term (Hormander.Interface.euclideanDivergence (Z L))
    (fun _ => 1) (divergence_contDiffOn hΩ (shortField_contDiffOn hΩ hX L))
      (generator_one Z v B 1 hneg)
  have hd' : HasGeneratorExpansion Ω Z v B 1 (-((v L : ℕ) : ℤ))
      (Hormander.Interface.euclideanDivergence (Z L)) :=
    hd.congr (fun x _ => (mul_one _).symm)
  have hterm : ∀ j : Fin n, ∀ K : ShortWord w s,
      HasGeneratorExpansion Ω Z v B 1 (-((v L : ℕ) : ℤ))
        (fun x => shortBracketCoefficient w X L (B j) K x * frameCoefficient Z B (Z K) j x) := by
    intro j K
    by_cases hweight : (v L : ℕ) + (v (B j) : ℕ) < (v K : ℕ)
    · have hc := shortBracketCoefficient_eq_zero_of_weight_lt w X L (B j) K hweight
      exact HasGeneratorExpansion.zero.congr (fun x _ => by
        simp only [congrFun hc x, Pi.zero_apply, zero_mul])
    · have hw : (v K : ℕ) ≤ (v L : ℕ) + (v (B j) : ℕ) := le_of_not_gt hweight
      have hw' : ((v K : ℕ) : ℤ) ≤ ((v L : ℕ) : ℤ) + ((v (B j) : ℕ) : ℤ) := by exact_mod_cast hw
      exact HasGeneratorExpansion.term _ _ (shortBracketCoefficient_contDiffOn hΩ hX hstep L (B j) K)
        (generator_mono le_rfl (by omega) (frameCoefficient_isGenerator Z v B j K))
  exact HasGeneratorExpansion.add hd' (generatorExpansion_sum Finset.univ _ (fun j _ =>
    generatorExpansion_sum Finset.univ _ (fun K _ => hterm j K)))

/-- The relative multiplier equals the actual first determinant
derivative wherever the frame is nondegenerate (BB (9.29), p. 429). -/
theorem fieldDerivative_frameDet_eq_multiplier {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s) (L : ShortWord w s)
    {x : Fin n → ℝ} (hx : x ∈ Ω) (hB : frameDet (shortField w X) B x ≠ 0) :
    fieldDerivative (shortField w X L) (frameDet (shortField w X) B) x =
      determinantMultiplier w X B L x * frameDet (shortField w X) B x :=
  fieldDerivative_frameDet_of_bracket_reduction B _ _ hB
    (fun j => ((shortField_contDiffOn hΩ hX (B j)).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp))
    (fun J => short_bracket_reduction hΩ hX hstep L J hx)

end RothschildStein.G4

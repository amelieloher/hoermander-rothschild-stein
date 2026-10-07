-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceParameters
public import RothschildStein.G4.WeightedBoxes

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The parameterized constant combination of actual vector fields. -/
def constantCombination {m n : ℕ}
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (p : (Fin m → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  ∑ j, p.1 j • Z j p.2

/-- Constant combinations depend smoothly on coefficients and
initial points (BB Remark 9.10, p. 404). -/
theorem constantCombination_contDiffOn {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (constantCombination Z) (univ ×ˢ Ω) := by
  apply ContDiffOn.sum
  intro j hj
  exact (((contDiff_apply ℝ ℝ j).comp contDiff_fst).contDiffOn).smul
    ((hZ j).comp contDiffOn_snd (fun p hp => hp.2))

/-- Rescale coefficients and time by inverse factors. -/
def flowScale {m n : ℕ} (θ : ℝ)
    (pt : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ)) :
    (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :=
  ((θ⁻¹ • pt.1.1, pt.1.2), θ * pt.2)

/-- The rescaling is smooth. -/
theorem flowScale_contDiff {m n : ℕ} (θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flowScale (m := m) (n := n) θ) := by
  have hα : ContDiff ℝ (⊤ : ℕ∞)
      (fun pt : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) => θ⁻¹ • pt.1.1) :=
    (contDiff_const (c := θ⁻¹)).smul contDiff_fst.fst
  have hβ : ContDiff ℝ (⊤ : ℕ∞)
      (fun pt : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) => θ * pt.2) :=
    (contDiff_const (c := θ)).mul contDiff_snd
  exact (hα.prodMk contDiff_fst.snd).prodMk hβ

/-- Rescaling the derivative preserves the prescribed constant coefficients. -/
theorem rescale_constantCombination_derivative {m n : ℕ}
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {θ t : ℝ} (hθ : 0 < θ) (a : Fin m → ℝ)
    (φ : ℝ → (Fin n → ℝ))
    (hd : HasDerivAt φ (constantCombination Z (θ⁻¹ • a, φ (θ * t))) (θ * t)) :
    HasDerivAt (fun v => φ (θ * v)) (∑ j, a j • Z j (φ (θ * t))) t := by
  have ht := (hasDerivAt_id t).const_mul θ
  have hh := hd.scomp t ht
  have heq : θ • constantCombination Z (θ⁻¹ • a, φ (θ * t)) =
      ∑ j, a j • Z j (φ (θ * t)) := by
    simp only [constantCombination, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hθ), one_mul]
  simpa only [mul_one, heq, Function.comp_def, id_eq] using hh

end RothschildStein.G4

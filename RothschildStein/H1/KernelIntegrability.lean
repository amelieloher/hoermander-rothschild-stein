-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.WordBounds
public import RothschildStein.G2.LocalPower

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A punctured continuous homogeneous kernel of degree above
minus Q is locally integrable. The value at zero has no effect on the
conclusion (BB Theorem 6.20(1), p. 269; Proposition 3.21, p. 105). -/
theorem locallyIntegrable_homogeneous_kernel (ν : G2.HomogeneousNorm G) {a : ℝ}
    (ha : -(G.homogeneousDimension : ℝ) < a) {f : (Fin N → ℝ) → ℝ}
    (hf : ContinuousOn f ({(0 : Fin N → ℝ)}ᶜ))
    (hh : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x) :
    LocallyIntegrable f := by
  let : NeZero N := ⟨Nat.ne_of_gt G.dimension_pos⟩
  obtain ⟨C, hC, hb⟩ := homogeneous_bound G ν a hf hh
  have hi : LocallyIntegrable (fun x => (ν x) ^ a) := by
    have h := (G2.locallyIntegrable_power_iff ν.gauge (-a)).mpr (by linarith)
    simpa only [neg_neg] using h
  have hiC : LocallyIntegrable (fun x => C * (ν x) ^ a) := hi.smul C
  apply hiC.mono (measurable_of_continuousOn_compl_singleton 0 hf).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (ν.gauge.2.1 x) _))]
  exact hb x hx

/-- Gamma and all words of weight less than two (in particular
the horizontal first derivatives) are locally integrable (BB p. 269). -/
theorem StandingHypotheses.wordDerivative_locallyIntegrable
    (H : StandingHypotheses G q) {Γ : (Fin N → ℝ) → ℝ}
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hh : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (I : List (Fin (q + 1))) (hI : differentialWordWeight I < 2) :
    LocallyIntegrable (wordDerivative H.fields I Γ) := by
  apply locallyIntegrable_homogeneous_kernel G H.norm
    (a := 2 - (G.homogeneousDimension : ℝ) - (differentialWordWeight I : ℝ))
    _ (H.wordDerivative_smooth_off_zero G hc I).continuousOn (H.wordDerivative_homogeneous G hc hh I)
  have hw : (differentialWordWeight I : ℝ) < 2 := by exact_mod_cast hI
  linarith

end RothschildStein.H1

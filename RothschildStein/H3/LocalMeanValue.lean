-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlCurveBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace RothschildStein.H3
open G2
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- The local mean-value inequality uses a containing closed control
ball and includes the drift-square term under the global control-norm
hypotheses (BB pp. 36–37). -/
theorem local_meanValue_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G driftWeight Y)
    {A : Set (Fin N → ℝ)} (hA : IsOpen A) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f A) {x y : Fin N → ℝ} {δ D : ℝ} {M : Fin q → ℝ}
    (hd : (controlDistance univ driftWeight Y x y).toReal < δ)
    (hball : {z | (controlDistance univ driftWeight Y x z).toReal ≤ δ} ⊆ A)
    (hM : ∀ z, (controlDistance univ driftWeight Y x z).toReal ≤ δ → ∀ i : Fin q,
      |fderiv ℝ f z (Y i.succ z)| ≤ M i)
    (hD : ∀ z, (controlDistance univ driftWeight Y x z).toReal ≤ δ →
      |fderiv ℝ f z (Y 0 z)| ≤ D) :
    |f y - f x| ≤ δ * (∑ i, M i) + δ ^ 2 * D := by
  have hδ : 0 < δ := ENNReal.toReal_nonneg.trans_lt hd
  have hxx : (controlDistance univ driftWeight Y x x).toReal ≤ δ := by
    rw [G1.controlDistance_self driftWeight Y (mem_univ x), ENNReal.toReal_zero]
    exact hδ.le
  have hM0 : 0 ≤ ∑ i, M i := Finset.sum_nonneg (fun i _ =>
    (abs_nonneg _).trans (hM x hxx i))
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD x hxx)
  have hfinite : controlDistance univ driftWeight Y x y ≠ ⊤ := by
    rw [H.distance_eq]
    exact ENNReal.ofReal_ne_top
  obtain ⟨r, hr, hrδ, γ, hγ, hγ0, hγ1⟩ := G1.exists_controlledCurve_of_controlDistance_lt
    ((ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr hd)
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (controlDistance univ driftWeight Y x (γ t)).toReal ≤ δ := by
    have hb := controlledCurve_stays_close_of_controlNorm H hγ ht
    rw [hγ0] at hb
    exact hb.trans hrδ.le
  have hγA : isControlledCurve A driftWeight Y r γ :=
    ⟨hγ.1, hγ.2.1, fun t ht => hball (hpath t ht), hγ.2.2.2⟩
  have hb := controlledCurve_field_sum_bound hA hf hγA
    (fun t ht i => hM _ (hpath t ht) i) (fun t ht => hD _ (hpath t ht))
  rw [hγ0, hγ1] at hb
  exact hb.trans (add_le_add (mul_le_mul_of_nonneg_right hrδ.le hM0)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hrδ.le 2) hD0))

end RothschildStein.H3

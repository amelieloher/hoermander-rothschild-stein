-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Quasidistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Left translation is a homeomorphism, directly from the group law
(BB Theorem 3.20, p. 105). -/
def gaugeLeftTranslation (x : Fin N → ℝ) : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) where
  toFun := G.mul x
  invFun := G.mul (G.inv x)
  left_inv y := by
    calc
      G.mul (G.inv x) (G.mul x y) = G.mul (G.mul (G.inv x) x) y := (G.assoc _ _ _).symm
      _ = G.mul 0 y := congrArg (fun z => G.mul z y) (G.inverse_left x)
      _ = y := G.zero_left y
  right_inv y := by
    calc
      G.mul x (G.mul (G.inv x) y) = G.mul (G.mul x (G.inv x)) y := (G.assoc _ _ _).symm
      _ = G.mul 0 y := congrArg (fun z => G.mul z y) (G.inverse_right x)
      _ = y := G.zero_left y
  continuous_toFun := continuous_pi fun j =>
    (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
      (continuous_pi fun k => Sum.casesOn k (fun _ => continuous_const) (fun l => continuous_apply l))
  continuous_invFun := continuous_pi fun j =>
    (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
      (continuous_pi fun k => Sum.casesOn k (fun _ => continuous_const) (fun l => continuous_apply l))

/-- Gauge balls are translated gauge sublevels (BB Thm 3.20, p. 105). -/
theorem gaugeBall_image (ν : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) (r : ℝ) :
    gaugeBall G ν x r = (G.mul x) '' {u | ν u < r} := by
  ext y
  change ν ((gaugeLeftTranslation G x).symm y) < r ↔ _
  constructor
  · intro h
    exact ⟨(gaugeLeftTranslation G x).symm y, h, (gaugeLeftTranslation G x).apply_symm_apply y⟩
  · rintro ⟨u, hu, rfl⟩
    change ν u < r at hu
    change ν ((gaugeLeftTranslation G x).symm ((gaugeLeftTranslation G x) u)) < r
    simpa only [(gaugeLeftTranslation G x).symm_apply_apply] using hu

/-- Closed gauge balls are translated closed sublevels (BB Thm 3.20, p. 105). -/
theorem gaugeClosedBall_image (ν : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) (r : ℝ) :
    gaugeClosedBall G ν x r = (G.mul x) '' {u | ν u ≤ r} := by
  ext y
  change ν ((gaugeLeftTranslation G x).symm y) ≤ r ↔ _
  constructor
  · intro h
    exact ⟨(gaugeLeftTranslation G x).symm y, h, (gaugeLeftTranslation G x).apply_symm_apply y⟩
  · rintro ⟨u, hu, rfl⟩
    change ν u ≤ r at hu
    change ν ((gaugeLeftTranslation G x).symm ((gaugeLeftTranslation G x) u)) ≤ r
    simpa only [(gaugeLeftTranslation G x).symm_apply_apply] using hu

/-- Every gauge ball is Euclidean open (BB Thm 3.20, p. 105). -/
theorem isOpen_gaugeBall {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) (r : ℝ) : IsOpen (gaugeBall G ν x r) := by
  exact (isOpen_lt hν.1 continuous_const).preimage (gaugeLeftTranslation G x).symm.continuous

/-- Every closed gauge ball is compact (BB Thm 3.20, p. 105). -/
theorem isCompact_gaugeClosedBall {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) (r : ℝ) : IsCompact (gaugeClosedBall G ν x r) := by
  rw [gaugeClosedBall_image]
  exact (isCompact_gauge_le hν r).image (gaugeLeftTranslation G x).continuous

/-- Positive-radius gauge balls contain their center (BB Thm 3.20, p. 105). -/
theorem center_mem_gaugeBall {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) : x ∈ gaugeBall G ν x r := by
  change ν (G.mul (G.inv x) x) < r
  have hi : G.mul (G.inv x) x = 0 := G.inverse_left x
  rw [hi, (hν.2.2.1 0).mpr rfl]
  exact hr

/-- Positive-radius gauge balls have positive volume (BB Thm 3.20, p. 105). -/
theorem volume_gaugeBall_pos {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r) : 0 < volume (gaugeBall G ν x r) :=
  (isOpen_gaugeBall G hν x r).measure_pos volume ⟨x, center_mem_gaugeBall G hν x hr⟩

/-- Gauge balls have finite volume (BB Thm 3.20, p. 105). -/
theorem volume_gaugeBall_ne_top {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) (r : ℝ) : volume (gaugeBall G ν x r) ≠ ⊤ := by
  apply ne_top_of_le_ne_top ((isCompact_gaugeClosedBall G hν x r).measure_ne_top (μ := volume))
  apply measure_mono
  intro y hy
  change gaugeDistance G ν y x ≤ r
  change gaugeDistance G ν y x < r at hy
  exact hy.le

end RothschildStein.G2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.WeightedSubcurves
public import RothschildStein.G1.IntegralCurveCosts

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- The square-root distance bound holds between any two times of a controlled curve, including coincident times (BB Remark 1.39, p. 22). -/
theorem controlled_curve_distance_between_times
    {Ω : Set (Fin n → ℝ)} {w : Fin q → ℕ+}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i,(w i : ℕ) ≤ 2) {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    controlDistance Ω w X (γ a) (γ b) ≤
      ENNReal.ofReal (δ * Real.sqrt |a-b|) := by
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hab),neg_sub,mul_comm] using
      G1.controlDistance_subcurve_le hw hγ ha.1 hab hb.2
  · rw [G1.controlDistance_symm Ω w X (γ a) (γ b)]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hba),mul_comm] using
      G1.controlDistance_subcurve_le hw hγ hb.1 hba ha.2

/-- Every parameter strictly larger than the control distance gives a connecting Euclidean-continuous curve with the same square-root modulus at every pair of times (BB Definition 1.38 and Remark 1.39, pp. 21–22). -/
theorem exists_controlled_curve_distance_certificate
    {Ω : Set (Fin n → ℝ)} {w : Fin q → ℕ+}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i,(w i : ℕ) ≤ 2) {x y : Fin n → ℝ} {δ : ℝ}
    (hd : controlDistance Ω w X x y < ENNReal.ofReal δ) :
    ∃ γ : ℝ → (Fin n → ℝ),isControlledCurve Ω w X δ γ ∧
      γ 0 = x ∧ γ 1 = y ∧ ContinuousOn γ (Icc 0 1) ∧
      ∀ a ∈ Icc (0 : ℝ) 1,∀ b ∈ Icc (0 : ℝ) 1,
        controlDistance Ω w X (γ a) (γ b) ≤
          ENNReal.ofReal (δ * Real.sqrt |a-b|) := by
  obtain ⟨ε,_,he,γ,hγ,h0,h1⟩ := G1.exists_controlledCurve_of_controlDistance_lt hd
  have hg := G1.isControlledCurve_mono_parameter hγ he.le
  refine ⟨γ,hg,h0,h1,?_,fun a ha b hb => controlled_curve_distance_between_times hw hg ha hb⟩
  simpa only [uIcc_of_le zero_le_one] using hg.2.1.continuousOn

end RothschildStein.S

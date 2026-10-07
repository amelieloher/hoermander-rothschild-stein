-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialBracketZero
public import RothschildStein.L1.CoordinateFieldJetClasses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The actual radial bracket identity gives the first ordinary jet
weight once the homogeneous bracket value is known. -/
theorem fieldJetClass_one_of_radial_bracket_values {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, u i • Z i u = u)
    (hZ0 : ∀ i, Z i 0 = Pi.single i 1)
    (hbr : ∀ i j k, (ω i : ℝ) + ω j < ω k →
      VectorField.lieBracket ℝ (Z i) (Z j) 0 k = 0) (i : Fin N) :
    fieldJetClass Ω ω (-(ω i : ℝ)) 1 (Z i) := by
  refine ⟨hZ i, ?_⟩
  intro k J hJ hw
  cases J with
  | nil =>
    exact (fieldJetClass_zero_order_of_coordinate_value Ω ω i (Z i) (hZ i) (hZ0 i)).2
      k [] (by simp) hw
  | cons j J =>
    have hnil : J = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hJ; omega)
    subst J
    have hk : (ω i : ℝ) + ω j < ω k := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero] at hw
      linarith
    have he := congrFun (radial_frame_bracket_zero Ω h0 Z hZ hrad hZ0 i j) k
    rw [hbr i j k hk] at he
    simp only [VectorField.lieBracket, fderiv_const_apply, zero_apply, zero_sub,
      Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at he
    have hd := ((hZ i).contDiffAt (Ω.isOpen.mem_nhds h0)).differentiableAt (by simp)
    rw [← fderiv_coordinate_apply (Z i) hd k (Pi.single j 1)] at he
    change (0 : ℝ) = 2 * -rsPartial [j] (fun u => Z i u k) 0 at he
    linarith
end RothschildStein.L1

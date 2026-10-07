-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FieldHomogeneity
public import RothschildStein.G1.TransportDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open Set
variable {N m : ℕ} (G : HomogeneousGroup N)

/-- Left invariant systems give left invariant control distance
(BB Theorem 3.54, (3.33), pp. 125–126; weighted curve transport included). -/
theorem controlDistance_leftInvariant (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, IsLeftInvariantField G (X i)) (z x y : Fin N → ℝ) :
    controlDistance univ w X (G.mul z x) (G.mul z y) = controlDistance univ w X x y := by
  apply G1.controlDistance_transport_eq isOpen_univ isOpen_univ
    ((contDiff_leftTranslation G z).of_le (by simp)).contDiffOn
    ((contDiff_leftTranslation G (G.inv z)).of_le (by simp)).contDiffOn
    (mapsTo_univ _ _) (mapsTo_univ _ _)
    (fun a _ => by rw [← mul_assoc G, inv_mul G, zero_mul G])
    (fun a _ i => hX i z a) (fun a _ i => hX i (G.inv z) a)
    (mem_univ x) (mem_univ y)

/-- Degree-p fields give the exact weighted control-distance scaling law
(BB Theorem 3.54, (3.37), pp. 126–127; the drift has degree two). -/
theorem controlDistance_homogeneous (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, IsHomogeneousField G (X i) (w i : ℕ))
    (t : ℝ) (ht : 0 < t) (x y : Fin N → ℝ) :
    controlDistance univ w X (G.dilate t x) (G.dilate t y) =
      ENNReal.ofReal t * controlDistance univ w X x y := by
  apply G1.controlDistance_scaled_transport_eq isOpen_univ isOpen_univ
    ((contDiff_dilate G t).of_le (by simp)).contDiffOn
    ((contDiff_dilate G t⁻¹).of_le (by simp)).contDiffOn
    (mapsTo_univ _ _) (mapsTo_univ _ _)
    (fun a _ => by rw [dilate_dilate G, inv_mul_cancel₀ ht.ne', dilate_one G]) ht
    (fun a _ i => by
      rw [(hasFDerivAt_dilate G t a).fderiv, dilationDifferential_apply, hX i t ht a,
        Real.rpow_natCast])
    (fun a _ i => by
      rw [(hasFDerivAt_dilate G t⁻¹ a).fderiv, dilationDifferential_apply,
        hX i t⁻¹ (inv_pos.mpr ht) a, Real.rpow_natCast])
    (mem_univ x) (mem_univ y)

/-- The exact gauge form follows from left invariance (BB p. 126). -/
theorem controlDistance_gauge (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, IsLeftInvariantField G (X i)) (x y : Fin N → ℝ) :
    controlDistance univ w X x y = controlDistance univ w X (G.mul (G.inv y) x) 0 := by
  have h := controlDistance_leftInvariant G w X hX (G.inv y) x y
  rw [inv_mul G] at h
  exact h.symm

end RothschildStein.G2

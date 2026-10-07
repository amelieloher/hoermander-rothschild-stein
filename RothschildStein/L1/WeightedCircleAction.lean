-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedFieldBrackets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- A field zero at the origin acts without losing another jet order.
The degree-zero endpoint uses its zero value directly. -/
theorem scalarJetClass_fieldDerivative_of_zero {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    (hV : circleFieldJetClass Ω ω a (p+1) V) (hf : scalarJetClass Ω ω b p f) :
    scalarJetClass Ω ω (a+b) p (fieldDerivative V f) := by
  cases p with
  | zero =>
    refine ⟨S.contDiffOn_fieldDerivative Ω V f hV.1.1 hf.1, ?_⟩
    intro J hJ hw
    have he : J = [] := List.length_eq_zero_iff.mp (by omega)
    subst J
    simp only [rsPartial, fieldDerivative, hV.2, map_zero]
  | succ p =>
    have hv : circleFieldJetClass Ω ω a (p+1) V :=
      ⟨fieldJetClass_order_mono hV.1 (by omega), hV.2⟩
    exact (circleScalarJetClass_fieldDerivative Ω h0 hv hf).1

/-- If the first field vanishes at the origin,
one fewer ordinary orders are needed in the other field. -/
theorem fieldJetClass_lieBracket_circle {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {V W : (Fin N → ℝ) → (Fin N → ℝ)}
    (hV : circleFieldJetClass Ω ω a (p+1) V) (hW : fieldJetClass Ω ω b p W) :
    fieldJetClass Ω ω (a+b) p (VectorField.lieBracket ℝ V W) := by
  refine ⟨lieBracket_contDiffOn Ω V W hV.1.1 hW.1, ?_⟩
  intro j
  have hcV : scalarJetClass Ω ω (a + ω j) (p+1) (fun x => V x j) :=
    ⟨contDiffOn_pi.mp hV.1.1 j, hV.1.2 j⟩
  have hcW : scalarJetClass Ω ω (b + ω j) p (fun x => W x j) :=
    ⟨contDiffOn_pi.mp hW.1 j, hW.2 j⟩
  have hs := scalarJetClass_fieldDerivative_of_zero Ω h0 hV hcW
  have ht := scalarJetClass_fieldDerivative Ω h0 hW hcV
  have hs' : scalarJetClass Ω ω (a+b+ω j) p (fieldDerivative V (fun x => W x j)) := by
    simpa only [add_assoc] using hs
  have ht' : scalarJetClass Ω ω (a+b+ω j) p (fieldDerivative W (fun x => V x j)) := by
    simpa only [add_assoc, add_comm, add_left_comm] using ht
  have hd := scalarJetClass_sub Ω h0 hs' ht'
  have he := scalarJetClass_congr Ω h0 hd (fun x hx =>
    lieBracket_coordinate_eq_fieldDerivative V W
      ((hV.1.1.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
      ((hW.1.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)) j)
  exact he.2
end RothschildStein.L1

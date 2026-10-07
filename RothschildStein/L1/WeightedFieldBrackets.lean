-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedFieldAction
public import RothschildStein.L1.WeightedJetNegation
public import RothschildStein.L1.PrefixDerivative
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The actual bracket coordinate is the difference of actual field actions. -/
theorem lieBracket_coordinate_eq_fieldDerivative {N : ℕ}
    (V W : (Fin N → ℝ) → (Fin N → ℝ)) {x : Fin N → ℝ}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) (j : Fin N) :
    VectorField.lieBracket ℝ V W x j =
      fieldDerivative V (fun y => W y j) x - fieldDerivative W (fun y => V y j) x := by
  simp only [fieldDerivative, fderiv_coordinate_apply W hW j, fderiv_coordinate_apply V hV j,
    VectorField.lieBracket, Pi.sub_apply]

/-- Actual smooth brackets remain smooth throughout the original open set. -/
theorem lieBracket_contDiffOn {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (V W : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) (hW : ContDiffOn ℝ (⊤ : ℕ∞) W Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (VectorField.lieBracket ℝ V W) Ω := by
  exact ((hW.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply hV).sub
    ((hV.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply hW)

/-- Actual brackets add weighted thresholds
and lose precisely one ordinary jet order. -/
theorem fieldJetClass_lieBracket {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {V W : (Fin N → ℝ) → (Fin N → ℝ)}
    (hV : fieldJetClass Ω ω a (p+1) V) (hW : fieldJetClass Ω ω b (p+1) W) :
    fieldJetClass Ω ω (a+b) p (VectorField.lieBracket ℝ V W) := by
  refine ⟨lieBracket_contDiffOn Ω V W hV.1 hW.1, ?_⟩
  intro j
  have hcV : scalarJetClass Ω ω (a + ω j) (p+1) (fun x => V x j) :=
    ⟨contDiffOn_pi.mp hV.1 j, hV.2 j⟩
  have hcW : scalarJetClass Ω ω (b + ω j) (p+1) (fun x => W x j) :=
    ⟨contDiffOn_pi.mp hW.1 j, hW.2 j⟩
  have hs := scalarJetClass_fieldDerivative Ω h0 (fieldJetClass_order_mono hV (by omega)) hcW
  have ht := scalarJetClass_fieldDerivative Ω h0 (fieldJetClass_order_mono hW (by omega)) hcV
  have hs' : scalarJetClass Ω ω (a+b+ω j) p (fieldDerivative V (fun x => W x j)) := by
    simpa only [add_assoc] using hs
  have ht' : scalarJetClass Ω ω (a+b+ω j) p (fieldDerivative W (fun x => V x j)) := by
    simpa only [add_assoc, add_comm, add_left_comm] using ht
  have hd := scalarJetClass_sub Ω h0 hs' ht'
  have he := scalarJetClass_congr Ω h0 hd (fun x hx =>
    lieBracket_coordinate_eq_fieldDerivative V W
      ((hV.1.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
      ((hW.1.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)) j)
  exact he.2
end RothschildStein.L1

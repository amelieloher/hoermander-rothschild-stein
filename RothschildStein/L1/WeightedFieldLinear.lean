-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedFieldProducts
public import RothschildStein.L1.WeightedJetNegation
public import RothschildStein.L1.AutomaticJetWeights
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- Constant scalar multiples preserve the field weight filtration. -/
theorem fieldJetClass_const_smul {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a : ℝ}
    {R : (Fin N → ℝ) → (Fin N → ℝ)} (hR : fieldJetClass Ω ω a p R) (c : ℝ) :
    fieldJetClass Ω ω a p (fun u => c • R u) := by
  have hc : scalarJetClass Ω ω 0 p (fun _ => c) :=
    ⟨contDiffOn_const, scalarJetVanishing_of_nonpos ω le_rfl _⟩
  simpa only [zero_add] using fieldJetClass_smul Ω h0 hc hR

/-- Finite sums preserve smooth finite field jet classes. -/
theorem fieldJetClass_sum {N p : ℕ} {ι : Type*} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (ω : Fin N → ℕ) (a : ℝ)
    (T : Finset ι) (R : ι → (Fin N → ℝ) → (Fin N → ℝ))
    (hR : ∀ i ∈ T, fieldJetClass Ω ω a p (R i)) :
    fieldJetClass Ω ω a p (fun u => ∑ i ∈ T, R i u) := by
  refine ⟨ContDiffOn.sum (fun i hi => (hR i hi).1), ?_⟩
  intro j
  have hj := scalarJetClass_sum Ω h0 ω (a + ω j) T
    (fun i u => R i u j) (fun i hi => ⟨contDiffOn_pi.mp (hR i hi).1 j, (hR i hi).2 j⟩)
  simpa only [Finset.sum_apply] using hj.2

/-- Subtracting fields preserves each fixed field weight class. -/
theorem fieldJetClass_sub {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a : ℝ}
    {R S : (Fin N → ℝ) → (Fin N → ℝ)} (hR : fieldJetClass Ω ω a p R)
    (hS : fieldJetClass Ω ω a p S) : fieldJetClass Ω ω a p (fun u => R u - S u) := by
  refine ⟨hR.1.sub hS.1, ?_⟩
  intro j
  have hj := scalarJetClass_sub Ω h0
    (show scalarJetClass Ω ω (a + ω j) p (fun u => R u j) from ⟨contDiffOn_pi.mp hR.1 j, hR.2 j⟩)
    (show scalarJetClass Ω ω (a + ω j) p (fun u => S u j) from ⟨contDiffOn_pi.mp hS.1 j, hS.2 j⟩)
  exact hj.2
end RothschildStein.L1

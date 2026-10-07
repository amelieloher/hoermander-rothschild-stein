-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Monoid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.P1
variable {ι E A : Type*} [MeasurableSpace E] {μ : Measure E}
  [NormedAddCommGroup A]

/-- Actual finite row integrability, preserving list multiplicities. -/
theorem integrable_listMapSum (l : List ι) (f : ι → E → A)
    (hf : ∀ i ∈ l, Integrable (f i) μ) :
    Integrable (fun x => (l.map (fun i => f i x)).sum) μ := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact integrable_zero E A μ
  | cons i l ih =>
    have hi := hf i List.mem_cons_self
    have ht := ih (fun j hj => hf j (List.mem_cons_of_mem i hj))
    simp only [List.map_cons, List.sum_cons]
    exact hi.add ht

variable [NormedSpace ℝ A]

/-- Actual integral linearity for a finite list of integrable rows. -/
theorem integral_listMapSum (l : List ι) (f : ι → E → A)
    (hf : ∀ i ∈ l, Integrable (f i) μ) :
    (∫ x, (l.map (fun i => f i x)).sum ∂μ) = (l.map (fun i => ∫ x, f i x ∂μ)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, integral_zero]
  | cons i l ih =>
    have hi := hf i List.mem_cons_self
    have ht := integrable_listMapSum l f (fun j hj => hf j (List.mem_cons_of_mem i hj))
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (f := f i) (g := fun x => (l.map (fun j => f j x)).sum) hi ht,
      ih (fun j hj => hf j (List.mem_cons_of_mem i hj))]

end RothschildStein.P1

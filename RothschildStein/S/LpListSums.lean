-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.S
variable {α ι τ : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- The Lp triangle inequality for a finite list sum retains
multiplicities of the commutator kernels (BB Thm 2.9, p. 73). -/
theorem eLpNorm_listSum_le (hp : 1 ≤ p) (l : List ι) (f : ι → α → ℝ) :
    eLpNorm (fun x => (l.map (fun i => f i x)).sum) p μ ≤
      (l.map (fun i => eLpNorm (f i) p μ)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons]
    have H := eLpNorm_add_le (f := f i) (g := fun x => (l.map (fun i => f i x)).sum) (μ := μ) hp
    exact H.trans (add_le_add le_rfl ih)

/-- A finite list sum of Lp errors tends to zero when each
summand does, with no artificial uniformity hypothesis
(BB Thm 2.9, p. 73; finite-sum). -/
theorem tendsto_eLpNorm_listSum_zero (hp : 1 ≤ p) (l : List ι)
    (f : ι → τ → α → ℝ) {L : Filter τ}
    (hf : ∀ i ∈ l, Tendsto (fun t => eLpNorm (f i t) p μ) L (𝓝 0)) :
    Tendsto (fun t => eLpNorm (fun x => (l.map (fun i => f i t x)).sum) p μ) L (𝓝 0) := by
  have ht : Tendsto (fun t => (l.map (fun i => eLpNorm (f i t) p μ)).sum) L (𝓝 0) := by
    induction l with
    | nil => simpa only [List.map_nil,List.sum_nil] using tendsto_const_nhds
    | cons i l ih =>
      simpa only [List.map_cons,List.sum_cons,zero_add] using
        (hf i List.mem_cons_self).add (ih (fun j hj => hf j (List.mem_cons_of_mem i hj)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall (fun _ => zero_le)
  · exact Eventually.of_forall (fun t => eLpNorm_listSum_le hp l (fun i => f i t))

end RothschildStein.S

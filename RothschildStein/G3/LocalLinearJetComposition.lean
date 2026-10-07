-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LocalScalarTaylor

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.G3

theorem iteratedFDeriv_comp_linear_at
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {n i : ℕ} (A : G →L[ℝ] E) (x : G)
    (hf : ContDiffAt ℝ n f (A x)) (hi : i ≤ n) :
    iteratedFDeriv ℝ i (f ∘ A) x =
      (iteratedFDeriv ℝ i f (A x)).compContinuousLinearMap (fun _ => A) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (n : WithTop ℕ∞)) le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  let s := Metric.ball (A x) r
  have hs : IsOpen s := Metric.isOpen_ball
  have hx : A x ∈ s := by simp [s, hr]
  have hpre : IsOpen (A ⁻¹' s) := hs.preimage A.continuous
  have he := A.iteratedFDerivWithin_comp_right (hfu.mono hru)
    hs.uniqueDiffOn hpre.uniqueDiffOn hx (i := i) (by exact_mod_cast hi)
  rw [iteratedFDerivWithin_of_isOpen i hpre hx,
    iteratedFDerivWithin_of_isOpen i hs hx] at he
  exact he

end RothschildStein.G3

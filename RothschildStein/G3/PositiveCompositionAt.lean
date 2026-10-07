-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FinitePositiveCompositionJets
@[expose] public section
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.G3

/-- Positive composition jets depend only on finite germs at the actual point. -/
theorem norm_positive_composition_jet_at_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {g : E → F} {x : E} {n : ℕ} (hn : 1 ≤ n)
    (hf : ContDiffAt ℝ n f (g x)) (hg : ContDiffAt ℝ n g x)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hfjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f (g x)‖ ≤ M)
    (hgjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ n.factorial*M*D^n := by
  obtain ⟨U,hU,hfU⟩ := hf.contDiffOn (m := (n : WithTop ℕ∞)) le_rfl (by simp)
  obtain ⟨ρ,hρ,hρU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨V,hV,hgV⟩ := hg.contDiffOn (m := (n : WithTop ℕ∞)) le_rfl (by simp)
  have hm : g ⁻¹' ball (g x) ρ ∈ 𝓝 x := hg.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hρ)
  obtain ⟨η,hη,hηsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hm)
  exact norm_local_finite_positive_composition_jet_le isOpen_ball isOpen_ball
    (hfU.mono hρU) (hgV.mono (fun y hy => (hηsub hy).1))
    (fun y hy => (hηsub hy).2) (by simpa using hη : x ∈ ball x η) hn hM hD hfjet hgjet
end RothschildStein.G3

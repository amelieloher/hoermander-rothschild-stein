-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameOpenInverse
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1

/-- One coefficient neighborhood works for every base point in
one smaller patch, with image in the joint inverse domain and the actual
left inverse identity throughout. -/
theorem exists_common_coefficient_patch {N : ℕ}
    (K Θ : ((Fin N → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ))
    (x : Fin N → ℝ) {O W : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hO : IsOpen O) (hpO : (x,0) ∈ O)
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K O) (hKx : K (x,0) = x)
    (hW : IsOpen W) (hpW : (x,x) ∈ W)
    (hleft : ∀ᶠ q in 𝓝 (x,0), Θ (q.1,K q) = q.2) :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ (⊤ : ℕ∞) K (ball x r ×ˢ ball 0 r) ∧
      ∀ q ∈ ball x r ×ˢ ball 0 r, q ∈ O ∧ (q.1,K q) ∈ W ∧ Θ (q.1,K q) = q.2 := by
  have hc : ContinuousAt (fun q => (q.1,K q)) (x,0) :=
    continuousAt_fst.prodMk ((hK.contDiffAt (hO.mem_nhds hpO)).continuousAt)
  have htarget : ∀ᶠ q in 𝓝 (x,0), (q.1,K q) ∈ W :=
    hc.preimage_mem_nhds (by simpa only [hKx] using hW.mem_nhds hpW)
  have hgood : {q : (Fin N → ℝ) × (Fin N → ℝ) |
      q ∈ O ∧ (q.1,K q) ∈ W ∧ Θ (q.1,K q) = q.2} ∈ 𝓝 (x,0) :=
    inter_mem (hO.mem_nhds hpO) (inter_mem htarget hleft)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hgood
  have hs : ball x r ×ˢ ball 0 r ⊆ {q | q ∈ O ∧ (q.1,K q) ∈ W ∧ Θ (q.1,K q) = q.2} := by
    intro q hq
    apply hsub
    rw [mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨hq.1,hq.2⟩
  exact ⟨r,hr,hK.mono (fun q hq => (hs hq).1),fun q hq => hs hq⟩
end RothschildStein.L1

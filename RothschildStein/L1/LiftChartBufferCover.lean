-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberAssemblyInterfaces
public import RothschildStein.L1.CompactPairedFamilyCover

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- The compact
paired-chart buffers of the coordinate data: the finite compatible cover of
`FixedLiftData.exists_compact_pairedJointShortChartCover`, indexed by `Fin N`
(BB pp. 448–449, 519–521). -/
theorem CoordinateApproximationData.compactChartBuffers_of_cover {n k s m : ℕ}
    {w : Fin (k+1) → ℕ+} {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (A : CoordinateApproximationData L M)
    (hn : 0 < n) (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hs : 1 ≤ s) :
    CompactChartBuffers A := by
  intro t ht ht1 K hK hKU
  have hKL : K ⊆ (L.U : Set (Fin (n+m) → ℝ)) :=
    fun ξ hξ => A.closure_subset_lift (subset_closure (hKU hξ))
  obtain ⟨Fo, Fl, R, S, hR, hcover⟩ := L.exists_compact_pairedJointShortChartCover hn
    (by omega) hΩ hX (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1) ht ht1 hK hKL
  let e : Fin S.card ≃ S := S.equivFin.symm
  refine ⟨S.card, fun i => basePoint (e i).1.1, fun i => (e i).1.1,
    fun i => Fo (e i).1, fun i => Fl (e i).1, ?_⟩
  intro η hη
  obtain ⟨ξ, hξS, hηξ⟩ := mem_iUnion₂.mp (hcover hη)
  obtain ⟨i, hi⟩ : ∃ i, e i = ⟨ξ, hξS⟩ := ⟨e.symm ⟨ξ, hξS⟩, e.apply_symm_apply _⟩
  refine ⟨i, ?_⟩
  show basePoint η ∈ closedBall (basePoint (e i).1.1) ((Fo (e i).1).R / 16) ∧
    η ∈ closedBall (e i).1.1 ((Fl (e i).1).R / 16)
  rw [hi]
  exact (hR ξ).2 η (ball_subset_closedBall hηξ)

end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedTaylorParameters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P1

variable {N : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- A coefficient smooth on its open chart
domain has a global smooth extension agreeing on a uniform model ball
over any compact endpoint parameter patch. This includes two endpoint
parameters; it uses the same cutoff construction as the existing
single-endpoint Taylor bound (BB Lemma 11.16, p. 548). -/
theorem exists_global_extension_generic_parameter
    (T : Set (P × (Fin N → ℝ))) (hT : IsOpen T)
    (A : P × (Fin N → ℝ) → ℝ) (hA : ContDiffOn ℝ (⊤ : ℕ∞) A T)
    (K : Set P) (hK : IsCompact K) (hKT : ∀ p ∈ K, (p, (0 : Fin N → ℝ)) ∈ T) :
    ∃ B : P × (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ K, ∀ u : Fin N → ℝ,
        ‖u‖ ≤ ε → B (p, u) = A (p, u) := by
  let S : Set (P × (Fin N → ℝ)) := (fun p => (p, (0 : Fin N → ℝ))) '' K
  have hS : IsCompact S := hK.image (continuous_id.prodMk continuous_const)
  have hST : S ⊆ T := by
    rintro _ ⟨p, hp, rfl⟩
    exact hKT p hp
  obtain ⟨Δ, hΔ, hΔT⟩ := hS.exists_cthickening_subset_open hT hST
  obtain ⟨χ, hχ, _, hχ0, hχ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) (s := (Metric.thickening Δ S)ᶜ)
    (t := Metric.cthickening (Δ / 2) S)
    Metric.isOpen_thickening.isClosed_compl Metric.isClosed_cthickening (by
      rw [Set.disjoint_compl_left_iff_subset]
      exact Metric.cthickening_subset_thickening' hΔ (by linarith) S)
  have hsupp : tsupport χ ⊆ T := by
    have hs : Function.support χ ⊆ Metric.thickening Δ S := by
      intro q hq
      by_contra hnot
      exact hq ((hχ0 q).mp hnot)
    exact (closure_mono hs).trans
      ((Metric.closure_thickening_subset_cthickening Δ S).trans hΔT)
  refine ⟨fun q => χ q * A q,
    RothschildStein.G1.cutoff_smul_contDiff hT A hA χ hχ hsupp,
    Δ / 2, by linarith, ?_⟩
  intro p hp u hu
  have hmem : (p, u) ∈ Metric.cthickening (Δ / 2) S := by
    refine Metric.mem_cthickening_of_dist_le (p, u) (p, (0 : Fin N → ℝ))
      (Δ / 2) S ⟨p, hp, rfl⟩ ?_
    simpa [Prod.dist_eq, dist_eq_norm] using hu
  simp only [(hχ1 _).mp hmem, one_mul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The local extension preserves every
weighted jet on the compact parameter patch because partial derivatives
depend only on the germ in the model coordinates. -/
theorem extension_preserves_weighted_jets (G : HomogeneousGroup N)
    (A B : P × (Fin N → ℝ) → ℝ) (K : Set P) (ε : ℝ) (hε : 0 < ε)
    (he : ∀ p ∈ K, ∀ u : Fin N → ℝ, ‖u‖ ≤ ε → B (p, u) = A (p, u))
    (low : ℕ) (hjet : ∀ p ∈ K, ∀ I : List (Fin N),
      (I.map G.weight).sum < low → rsPartial I (fun u => A (p, u)) 0 = 0) :
    ∀ p ∈ K, ∀ I : List (Fin N), (I.map G.weight).sum < low →
      rsPartial I (fun u => B (p, u)) 0 = 0 := by
  intro p hp I hI
  have hev : (fun u => B (p, u)) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun u => A (p, u) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Fin N → ℝ) hε] with u hu
    exact he p hp u (mem_ball_zero_iff.mp hu).le
  rw [(rsPartial_eventuallyEq I hev).eq_of_nhds]
  exact hjet p hp I hI

end RothschildStein.P1

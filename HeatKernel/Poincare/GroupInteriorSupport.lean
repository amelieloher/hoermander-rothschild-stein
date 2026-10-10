-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.BallTopology
public import RothschildStein.G2.InvariantFields
public import RothschildStein.G2.MollifierScale

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.mul RothschildStein.HomogeneousGroup.inv
open Set RothschildStein
namespace HeatKernel

/-- Compact interior sets have a common identity neighborhood whose inverse translates
stay in the given open set. -/
theorem exists_gauge_radius_inverse_translation_subset
    {N : ℕ} (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G)
    {K U : Set (Fin N → ℝ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin N → ℝ, ν a < δ →
      ∀ x ∈ K, G.mul (G.inv a) x ∈ U := by
  let P := fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul (G.inv p.1) p.2
  have hInv : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.inv p.1) :=
    (G2.contDiff_inv G).continuous.comp continuous_fst
  have hpair : Continuous
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (G.inv p.1, p.2)) :=
    hInv.prodMk continuous_snd
  have hP : Continuous P := (G2.contDiff_mul G).continuous.comp hpair
  have hp : ({0} : Set (Fin N → ℝ)) ×ˢ K ⊆ P ⁻¹' U := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    have ha0 : a = 0 := ha
    subst a
    simpa only [mem_preimage, P, G2.inv_zero, G2.zero_mul] using hKU hx
  obtain ⟨u, v, hu, _, h0u, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hU.preimage hP) hp
  obtain ⟨δ, hδ, hδu⟩ := G2.gaugeBall_basis ν.gauge hu (x := (0 : Fin N → ℝ)) (h0u (by simp))
  refine ⟨δ, hδ, ?_⟩
  intro a ha x hx
  have hau : a ∈ u := hδu (by
    change ν (G.mul (G.inv 0) a) < δ
    simpa only [G2.inv_zero, G2.zero_mul] using ha)
  exact huv (show (a,x) ∈ u ×ˢ v from ⟨hau, hKv hx⟩)

/-- The translated topological support of a scaled group mollifier is contained in
its closed gauge sublevel. -/
theorem tsupport_groupMollifierScale_kernel_subset
    {N : ℕ} (G : HomogeneousGroup N) {ν : G2.HomogeneousNorm G}
    (φ : G2.GroupMollifier G ν) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    tsupport (fun z => G2.groupMollifierScale G φ ε (G.mul x (G.inv z))) ⊆
      {z | ν (G.mul x (G.inv z)) ≤ ε} := by
  apply closure_minimal
  · intro z hz
    have hh : ν (G.mul x (G.inv z)) < ε :=
      G2.support_groupMollifierScale_subset G φ hε hz
    exact hh.le
  · exact isClosed_le
      (ν.gauge.1.comp ((G2.contDiff_leftTranslation G x).continuous.comp
        (G2.contDiff_inv G).continuous)) continuous_const

/-- Shrinking group kernels have translated support uniformly inside the domain on
any compact interior set. -/
theorem exists_groupMollifierScale_kernel_interior_support
    {N : ℕ} (G : HomogeneousGroup N) {ν : G2.HomogeneousNorm G}
    (φ : G2.GroupMollifier G ν) {K U : Set (Fin N → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ x ∈ K,
      tsupport (fun z => G2.groupMollifierScale G φ ε (G.mul x (G.inv z))) ⊆ U := by
  obtain ⟨δ, hδ, ht⟩ := exists_gauge_radius_inverse_translation_subset G ν hK hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ x hx z hz
  have hg := tsupport_groupMollifierScale_kernel_subset G φ hε x hz
  change ν (G.mul x (G.inv z)) ≤ ε at hg
  have hm := ht (G.mul x (G.inv z)) (hg.trans_lt hεδ) x hx
  simpa only [G2.inv_product, G2.inv_inv, G2.mul_assoc, G2.inv_mul, G2.mul_zero] using hm

end HeatKernel

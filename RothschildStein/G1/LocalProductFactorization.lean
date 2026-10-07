-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ProductFactorization
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology BigOperators

namespace RothschildStein.G1

section Cutoff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth cut-off supported in the local smoothness domain
extends the product smoothly by zero (BB Prop 1.50, pp. 28–29). -/
theorem cutoff_smul_contDiff {U : Set E} (hU : IsOpen U)
    (G : E → F) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (φ : E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsupp : tsupport φ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => φ q • G q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q ∈ tsupport φ
  · exact hφ.contDiffAt.smul (hG.contDiffAt (hU.mem_nhds (hsupp hq)))
  · apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => (0 : F)) q).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with y hy
    simp only [hy, Pi.zero_apply, zero_smul]

end Cutoff

section Product
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [CompleteSpace F]

/-- The product factorization is local: on any open smoothness
domain, all vanishing parameter hyperplanes yield a smooth factor on a
smaller neighborhood of the reference point. No global flow domain is
required (BB Prop 1.50, pp. 28–29). -/
theorem exists_local_smooth_productFactor {n : ℕ} (S : Finset (Fin n))
    {U : Set ((Fin n → ℝ) × E)} (hU : IsOpen U)
    (G : ((Fin n → ℝ) × E) → F) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hzero : ∀ q ∈ U, ∀ i ∈ S, q.1 i = 0 → G q = 0)
    (q₀ : (Fin n → ℝ) × E) (hq₀ : q₀ ∈ U) :
    ∃ V : Set ((Fin n → ℝ) × E), IsOpen V ∧ q₀ ∈ V ∧ V ⊆ U ∧
      ∃ H : ((Fin n → ℝ) × E) → F, ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
        ∀ q ∈ V, G q = (∏ i ∈ S, q.1 i) • H q := by
  classical
  obtain ⟨φ, hsupp, _, hφ, _, hφq⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hq₀)
  let K : ((Fin n → ℝ) × E) → F := fun q => φ q • G q
  have hK : ContDiff ℝ (⊤ : ℕ∞) K := cutoff_smul_contDiff hU G hG φ hφ hsupp
  have hz : ∀ q i, i ∈ S → q.1 i = 0 → K q = 0 := by
    intro q i hi hqi
    by_cases hq : q ∈ U
    · simp only [K, hzero q hq i hi hqi, smul_zero]
    · have hφzero : φ q = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hq (hsupp h))
      simp only [K, hφzero, zero_smul]
  obtain ⟨H, hH, heq⟩ := exists_smooth_productFactor S K hK hz
  let V := U ∩ {q | φ q ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_ne.preimage hφ.continuous)
  refine ⟨V, hV, ⟨hq₀, by change φ q₀ ≠ 0; rw [hφq]; exact one_ne_zero⟩,
    inter_subset_left, fun q => (φ q)⁻¹ • H q, ?_, ?_⟩
  · exact (hφ.contDiffOn.inv (fun q hq => hq.2)).smul hH.contDiffOn
  · intro q hq
    have hφne : φ q ≠ 0 := hq.2
    have hh := congrArg (fun v : F => (φ q)⁻¹ • v) (heq q)
    change (φ q)⁻¹ • (φ q • G q) = _ at hh
    rw [inv_smul_smul₀ hφne] at hh
    exact hh.trans (smul_comm _ _ _)

end Product

end RothschildStein.G1

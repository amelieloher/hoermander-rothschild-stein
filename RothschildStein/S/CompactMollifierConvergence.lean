-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactSobolevRestriction
public import RothschildStein.S.SobolevMollifierConvergence
public import RothschildStein.S.MollifierCompactAllDimensions
public import RothschildStein.S.SobolevSubtraction
public import RothschildStein.S.TestSobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Function
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Ordinary mollifications of compact interior Sobolev data converge in the full-domain norm (BB Corollary 2.10, p. 73; Proposition 8.49, p. 379). -/
theorem tendsto_sobolevXENorm_mollifier_compact
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (hpt : p ≠ ⊤) {f : (Fin n → ℝ) → ℝ}
    (hf : memSobolevX w X Ω k p f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ω) :
    Tendsto (fun ε : ℝ => sobolevXENorm w X Ω k p
      (fun x => f x-euclideanRegularize n f ε x)) (𝓝[>] 0) (𝓝 0) := by
  classical
  have hi : (Ω : Set (Fin n → ℝ)).indicator f = f := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))).symm
  have hl : LocallyIntegrable f volume := by
    have H := (memLp_zeroExtension_iff Ω.isOpen.measurableSet f).mpr hf.1
    rw [hi] at H
    exact H.locallyIntegrable Fact.out
  obtain ⟨V,hV,hfV,hVΩ,hcV⟩ :=
    exists_open_between_and_isCompact_closure hc.isCompact Ω.isOpen hs
  let U : Opens (Fin n → ℝ) := ⟨V,hV⟩
  obtain ⟨δ,hd,hδ⟩ := exists_euclideanRegularize_support_inside_all_dimensions hc hV hfV
  have H := tendsto_sobolevXENorm_mollifier_local w X Ω U hX hcV hVΩ k hpt hf
  simp only [hi] at H
  apply H.congr'
  filter_upwards [Ioo_mem_nhdsGT hd] with ε he
  obtain ⟨hsm,hcm⟩ := euclideanRegularize_smooth_compact_all_dimensions hl hc he.1
  have hmV : tsupport (euclideanRegularize n f ε) ⊆ U := hδ ε he.1 he.2.le
  let φ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    ⟨euclideanRegularize n f ε,hsm,hcm,hmV.trans (subset_closure.trans hVΩ)⟩
  have hmf : memSobolevX w X Ω k p (euclideanRegularize n f ε) :=
    test_memSobolevX w Ω X hX k p φ
  have heq := sobolevXENorm_eq_of_compact_support w X Ω U
    (subset_closure.trans hVΩ) k (memSobolevX_sub w X Ω hX k hf hmf)
    (hc.sub hcm) ((tsupport_sub f (euclideanRegularize n f ε)).trans (union_subset hfV hmV))
  exact heq.symm

end RothschildStein.S

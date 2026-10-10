-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierSubstitution
public import RothschildStein.G2.ConvolutionSmooth
public import RothschildStein.G2.MollifierBound

/-! Small group regularizations preserve compact support inside an open set. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter
open scoped Topology
namespace HeatKernel

/-- A compactly supported input contained in an open set has all sufficiently small
positive group regularizations supported in that open set. -/
theorem eventually_tsupport_groupRegularize_subset {N : ℕ} (G : HomogeneousGroup N)
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    {f : (Fin N → ℝ) → ℝ} (hf : HasCompactSupport f)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hs : tsupport f ⊆ U) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, tsupport (G2.groupRegularize G φ f ε) ⊆ U := by
  let H : ℝ × ((Fin N → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
    fun p => G.mul (G.dilate p.1 p.2.1) p.2.2
  have hd : Continuous (fun p : ℝ × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      G.dilate p.1 p.2.1) := by
    apply continuous_pi
    intro j
    exact (continuous_fst.pow (G.weight j)).mul
      ((continuous_apply j).comp (continuous_fst.comp continuous_snd))
  have hH : Continuous H := by
    apply continuous_pi
    intro j
    exact (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
      (continuous_pi fun i => Sum.casesOn i
        (fun k => (continuous_apply k).comp hd)
        (fun k => (continuous_apply k).comp (continuous_snd.comp continuous_snd)))
  have he : ∀ᶠ ε : ℝ in 𝓝 0, ∀ p ∈ tsupport φ ×ˢ tsupport f, H (ε,p) ∈ U := by
    apply (φ.compact.prod hf).eventually_forall_of_forall_eventually
    intro p hp
    apply (hH.continuousAt).eventually (hU.mem_nhds ?_)
    simpa only [H, G2.zero_dilate, G2.zero_mul] using hs hp.2
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hε hpos
  change 0 < ε at hpos
  let K : Set (Fin N → ℝ) :=
    (fun p : (Fin N → ℝ) × (Fin N → ℝ) => H (ε,p)) '' (tsupport φ ×ˢ tsupport f)
  have hK : IsCompact K := (φ.compact.prod hf).image
    (hH.comp (continuous_const.prodMk continuous_id))
  have hKU : K ⊆ U := by
    rintro x ⟨p, hp, rfl⟩
    exact hε p hp
  apply subset_trans (closure_minimal ?_ hK.isClosed) hKU
  intro x hx
  obtain ⟨⟨y,z⟩, ⟨hy,hz⟩, rfl⟩ :=
    G2.support_groupConvolution_subset G (G2.groupMollifierScale G φ ε) f hx
  have hp : φ (G.dilate ε⁻¹ y) ≠ 0 := by
    intro h
    apply hy
    simp only [G2.groupMollifierScale, h, mul_zero]
  refine ⟨(G.dilate ε⁻¹ y,z), ⟨subset_closure hp, subset_closure hz⟩, ?_⟩
  change G.mul (G.dilate ε (G.dilate ε⁻¹ y)) z = G.mul y z
  rw [G2.dilate_dilate, mul_inv_cancel₀ hpos.ne', G2.dilate_one]

end HeatKernel

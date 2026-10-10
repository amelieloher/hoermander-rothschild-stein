-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.WeakHorizontalGradient
public import HeatKernel.Form.CompactGradientApproximation
public import HeatKernel.Form.GraphForm
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Compact horizontal Lipschitz functions belong to the closed horizontal energy graph. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators
namespace HeatKernel

/-- Bounded weak derivatives of a compactly supported function belong to L². -/
theorem memLp_weakWordDeriv_of_compact_support_of_ae_bound {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin q))
    {f g : (Fin N → ℝ) → ℝ} (hc : HasCompactSupport f)
    (hg : hasWeakWordDeriv X ⊤ I f g) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, |g x| ≤ C) : MemLp g 2 volume := by
  let U : Opens (Fin N → ℝ) := ⟨(tsupport f)ᶜ, isClosed_tsupport f |>.isOpen_compl⟩
  have hfzero : f =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] fun _ => 0 :=
    ae_restrict_of_forall_mem U.isOpen.measurableSet (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have hgzero := S.hasWeakWordDeriv_locality X ⊤ U (subset_univ _) hg hfzero
  have hgzero' : ∀ᵐ x ∂volume, x ∉ tsupport f → g x = 0 :=
    (ae_restrict_iff' U.isOpen.measurableSet).mp hgzero
  have hmeas : AEStronglyMeasurable g volume :=
    (locallyIntegrableOn_univ.mp (by simpa only [Opens.coe_top] using hg.2.1)).aestronglyMeasurable
  apply (memLp_indicator_const 2 (isClosed_tsupport f).measurableSet C
    (Or.inr hc.measure_lt_top.ne)).mono' hmeas
  filter_upwards [hb, hgzero'] with x hx hz
  by_cases hxs : x ∈ tsupport f
  · simpa only [indicator_of_mem hxs, Real.norm_eq_abs] using hx
  · simp only [indicator_of_notMem hxs, hz hxs, norm_zero]
    exact le_rfl

/-- A compactly supported horizontal Lipschitz function has a representative in the closed
energy graph, and its energy gradient retains the sharp joint pointwise bound. -/
theorem exists_energyGraph_of_compact_horizontalLipschitz {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (L : ℝ≥0) {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hLip : ∀ x y, edist (f x) (f y) ≤ (L : ℝ≥0∞) * horizontalL2Distance (G.horizontalFields hq) x y) :
    ∃ u : energyGraph (N := N) ⊤ (G.horizontalFields hq),
      energyInclusion ⊤ (G.horizontalFields hq) u =ᵐ[volume] f ∧
      ∀ᵐ x ∂volume, Real.sqrt (∑ i, (energyGradient ⊤ (G.horizontalFields hq) u i x) ^ 2) ≤ L := by
  obtain ⟨g, hg, hb⟩ := exists_weak_horizontal_gradient G hq L hf hLip
  have hgb : ∀ i, ∀ᵐ x ∂volume, |g i x| ≤ L := by
    intro i
    filter_upwards [hb] with x hx
    exact (abs_control_le_controlNorm (fun i _ => g i x) i 0).trans hx
  have hgp : ∀ i, MemLp (g i) 2 volume := fun i =>
    memLp_weakWordDeriv_of_compact_support_of_ae_bound (G.horizontalFields hq) [i] hc (hg i) (hgb i)
  have hfp : MemLp f 2 (volume.restrict (⊤ : Opens (Fin N → ℝ))) :=
    hf.memLp_of_hasCompactSupport hc
  have hgp' : ∀ i, MemLp (g i) 2 (volume.restrict (⊤ : Opens (Fin N → ℝ))) := by
    intro i
    simpa only [Opens.coe_top, Measure.restrict_univ] using hgp i
  let v : GradientSpace (N := N) ⊤ q := WithLp.toLp 2
    (hfp.toLp f, WithLp.toLp 2 (fun i => (hgp' i).toLp (g i)))
  have hv : v ∈ weakGradientGraph ⊤ (G.horizontalFields hq)
      (fun i => (G.horizontalFields_contDiff hq i).contDiffOn) := by
    intro i
    exact S.hasWeakWordDeriv_congr_ae (G.horizontalFields hq) ⊤ (hg i)
      hfp.coeFn_toLp.symm (hgp' i).coeFn_toLp.symm
  have hvf : v.fst =ᵐ[volume] f := by
    simpa only [v, WithLp.toLp_fst, Opens.coe_top, Measure.restrict_univ] using hfp.coeFn_toLp
  have hve := mem_energyGraph_of_compact_weakGradient (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) ⟨v, hv⟩ hc hvf
  let u : energyGraph (N := N) ⊤ (G.horizontalFields hq) := ⟨v, hve⟩
  have hgrad : ∀ i, energyGradient ⊤ (G.horizontalFields hq) u i =ᵐ[volume] g i := by
    intro i
    simpa only [u, energyGradient_apply, v, WithLp.toLp_snd, PiLp.toLp_apply,
      Opens.coe_top, Measure.restrict_univ] using (hgp' i).coeFn_toLp
  refine ⟨u, hvf, ?_⟩
  have hall := ae_all_iff.mpr hgrad
  filter_upwards [hall, hb] with x hx hbx
  simpa only [hx] using hbx

/-- Compactly supported Lipschitz functions for the horizontal metric belong to the
coordinate horizontal energy graph with their sharp gradient bound. -/
theorem CarnotPoint.exists_energyGraph_of_compact_lipschitz {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {L : ℝ≥0} {f : CarnotPoint G hq hqpos hspan → ℝ}
    (hf : LipschitzWith L f) (hc : HasCompactSupport f) :
    ∃ u : energyGraph (N := N) ⊤ (G.horizontalFields hq),
      energyInclusion ⊤ (G.horizontalFields hq) u =ᵐ[MeasureTheory.volume] f ∧
      ∀ᵐ x ∂MeasureTheory.volume,
        Real.sqrt (∑ i, (energyGradient ⊤ (G.horizontalFields hq) u i x) ^ 2) ≤ L :=
  exists_energyGraph_of_compact_horizontalLipschitz G hq L hf.continuous hc (fun x y => hf x y)

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalHolderRegularity
public import RothschildStein.H3.RealRepresentativeOverlap
public import RothschildStein.Definitions.representsDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.H3

/-- All relatively compact Holder representatives glue to one
actual representative of the original distribution. Compact support of
each test places it in one such patch, so no countability premise is
needed for the final distribution identity. -/
theorem global_holder_representative_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm)
    (Ω : Opens (Fin N → ℝ)) {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin N → ℝ) → ℝ)
    (hf : memHolderXLoc driftWeight H.fields (controlDistance univ driftWeight H.fields) Ω 0 a f)
    (heq : hasDistributionEquationWithDrift Ω H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) T f) :
    ∃ u : (Fin N → ℝ) → ℝ, representsDistribution Ω T u ∧
      memHolderXLoc driftWeight H.fields (controlDistance univ driftWeight H.fields) Ω 2 a u := by
  classical
  let I := {U : Opens (Fin N → ℝ) // IsCompact (closure (U : Set (Fin N → ℝ))) ∧
    closure (U : Set (Fin N → ℝ)) ⊆ Ω}
  have hex (i : I) := relCompact_holder_representative_of_controlNorm G H K hQ C φ Ω i.val
    i.property.1 i.property.2 ha ha1 T f hf heq
  choose g hg hrep using hex
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  have hgc (i : I) : ContinuousOn (g i) (i.val : Set (Fin N → ℝ)) :=
    RothschildStein.S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D (subset_univ _)
      (show 0 < (a : ℝ) from ha) (hg i).1
  have hsub (i : I) : i.val ≤ Ω := subset_closure.trans i.property.2
  have hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i : I, x ∈ i.val := by
    intro x hx
    obtain ⟨U, hU, hxU, hclU, hcU⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := x)) Ω.isOpen (singleton_subset_iff.mpr hx)
    exact ⟨⟨⟨U, hU⟩, hcU, hclU⟩, hxU (mem_singleton x)⟩
  have hcompat (i j : I) : EqOn (g i) (g j)
      ((i.val : Set (Fin N → ℝ)) ∩ (j.val : Set (Fin N → ℝ))) :=
    real_distribution_representatives_agree Ω i.val j.val (hsub i) (hsub j)
      (g i) (g j) (hgc i) (hgc j) T (hrep i) (hrep j)
  let u := fun x => if hx : x ∈ (Ω : Set (Fin N → ℝ)) then g (Classical.choose (hcover x hx)) x else 0
  have hueq (i : I) : EqOn u (g i) (i.val : Set (Fin N → ℝ)) := by
    intro x hx
    have hxΩ : x ∈ (Ω : Set (Fin N → ℝ)) := hsub i hx
    dsimp only [u]
    rw [dite_eq_left hxΩ]
    exact hcompat (Classical.choose (hcover x hxΩ)) i
      ⟨Classical.choose_spec (hcover x hxΩ), hx⟩
  have huc : ContinuousOn u (Ω : Set (Fin N → ℝ)) := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    have hmem : ∀ᶠ y in 𝓝 x, y ∈ (i.val : Set (Fin N → ℝ)) := i.val.isOpen.mem_nhds hi
    have hev : u =ᶠ[𝓝 x] g i := hmem.mono (fun y hy => hueq i hy)
    exact ((hgc i).continuousAt (i.val.isOpen.mem_nhds hi)).congr_of_eventuallyEq hev |>.continuousWithinAt
  have hul : LocallyIntegrableOn u (Ω : Set (Fin N → ℝ)) volume :=
    huc.locallyIntegrableOn Ω.isOpen.measurableSet
  refine ⟨u, ⟨hul, ?_⟩, ?_⟩
  · ext ψ
    obtain ⟨U, hU, hsU, hclU, hcU⟩ := exists_open_between_and_isCompact_closure
      ψ.hasCompactSupport Ω.isOpen ψ.tsupport_subset
    let i : I := ⟨⟨U, hU⟩, hcU, hclU⟩
    let ψU : TestFunction i.val ℝ (⊤ : ℕ∞) := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hsU⟩
    have hext : (TestFunction.monoCLM ℝ ψU : TestFunction Ω ℝ (⊤ : ℕ∞)) = ψ := by
      ext x
      simp [TestFunction.monoCLM_apply, hsub i, ψU]
    rw [Distribution.ofFun_apply hul]
    have hh := hrep i ψU
    rw [hext] at hh
    apply hh.trans
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul]
    change ψ x * g i x = ψ x * u x
    by_cases hx : x ∈ U
    · rw [hueq i hx]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsU ht)), zero_mul, zero_mul]
  · intro U hKU hKUΩ
    let i : I := ⟨U, hKU, hKUΩ⟩
    refine ⟨?_, ?_⟩
    · rw [RothschildStein.S.holderENorm_congr _ a (U : Set (Fin N → ℝ)) u (hueq i)]
      exact (hg i).1
    · intro J hJ
      obtain ⟨v, hv, hvn⟩ := (hg i).2 J hJ
      exact ⟨v, intrinsic_word_congr_input H.fields U J (hueq i).symm hv, hvn⟩

end RothschildStein.H3

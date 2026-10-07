-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderDistributionParticular
public import RothschildStein.H3.CutoffSourceGlobalHolder
public import RothschildStein.H3.FrozenDistributionEquationRestriction
public import RothschildStein.H3.FrozenDriftEquationRestriction
public import RothschildStein.H3.IntrinsicWordRestriction
public import RothschildStein.H3.HolderPotentialSolver
public import RothschildStein.H3.QuasiballOriginFacts
public import RothschildStein.Definitions.memHolderXLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Arbitrary locally Holder forcing gives an actual fixed
weight-two Holder representative on every relatively compact interior
domain. The cutoff, particular solution and homogeneous remainder are
constructed from the original distribution equation. -/
theorem relCompact_holder_representative_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (φ : G2.GroupMollifier G C.norm)
    (Ω U : Opens (Fin N → ℝ))
    (hK : IsCompact (closure (U : Set (Fin N → ℝ))))
    (hKΩ : closure (U : Set (Fin N → ℝ)) ⊆ Ω)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin N → ℝ) → ℝ)
    (hf : memHolderXLoc driftWeight H.fields (controlDistance univ driftWeight H.fields) Ω 0 a f)
    (heq : hasDistributionEquationWithDrift Ω H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) T f) :
    ∃ w : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a w ∧
      ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞), T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x * w x := by
  obtain ⟨V₀, hV₀, hKUV, hclV, hcV⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  let V : Opens (Fin N → ℝ) := ⟨V₀, hV₀⟩
  obtain ⟨W, hW, hVW, hclW, hcW⟩ := exists_open_between_and_isCompact_closure hcV Ω.isOpen hclV
  obtain ⟨χ, hχ, _, hs, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW hcV.isClosed hVW
  obtain ⟨A₀, hA₀, hWA, hclA, hcA⟩ := exists_open_between_and_isCompact_closure hcW Ω.isOpen hclW
  let A : Opens (Fin N → ℝ) := ⟨A₀, hA₀⟩
  let χA : TestFunction A ℝ (⊤ : ℕ∞) :=
    ⟨χ, hχ, by simpa [HasCompactSupport, tsupport, hs] using hcW,
      by rw [tsupport, hs]; exact hWA⟩
  let F := fun x => χ x * f x
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  have hFn := cutoff_source_global_holder_finite_of_controlNorm G H C A (by exact_mod_cast ha1.le)
    f (hf A hcA hclA).1 χA
  have hFc : Continuous F := continuousOn_univ.mp
    (RothschildStein.S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D (subset_univ _)
      (show 0 < (a : ℝ) from ha) hFn)
  have hFcompact : HasCompactSupport F := χA.hasCompactSupport.mul_right
  obtain ⟨R, hR⟩ := χA.hasCompactSupport.bddAbove_image C.norm.gauge.1.continuousOn
  let ρ := max 1 R + 1
  have hρ : 0 < ρ := by dsimp [ρ]; linarith [le_max_left 1 R]
  have hsupport : tsupport (χA : (Fin N → ℝ) → ℝ) ⊆ {x | C.norm x < ρ} := by
    intro x hx
    change C.norm.toFun x < ρ
    have hh := hR ⟨x, hx, rfl⟩
    dsimp [ρ]
    linarith [le_max_right 1 R]
  let B := quasiballDomain G C.norm 0 ρ
  have hVB : (V : Set (Fin N → ℝ)) ⊆ B := by
    intro x hx
    have hxW : x ∈ tsupport (χA : (Fin N → ℝ) → ℝ) := by
      change x ∈ closure (Function.support χ)
      rw [hs]
      exact subset_closure (hVW (subset_closure hx))
    have hh := hsupport hxW
    change C.norm (G.mul (G.inv 0) x) < ρ
    rw [G2.inv_zero, G2.zero_mul]
    exact hh
  obtain ⟨c, _hc, hsolve⟩ := holder_potential_solver_of_controlNorm G H K hQ C φ hρ ha ha1
  obtain ⟨hv, hveq, _hvn⟩ := hsolve F hFc hFcompact (tsupport_mul_subset_left.trans hsupport) hFn
  let v := G2.groupConvolution G F K
  have hvl : LocallyIntegrableOn v (B : Set (Fin N → ℝ)) volume :=
    (RothschildStein.S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D (subset_univ _)
      (show 0 < (a : ℝ) from ha) hv.1).locallyIntegrableOn B.isOpen.measurableSet
  have heV := frozen_drift_equation_restrict B V hVB H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) v F hvl hveq
  have hVΩ : V ≤ Ω := subset_closure.trans hclV
  have hT := frozen_distribution_drift_equation_restrict Ω V hVΩ H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) T f heq
  have hFae : F =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    change χ x * f x = f x
    rw [(hone x).mp (subset_closure hx), one_mul]
  have hFF : Distribution.ofFun V F volume (⊤ : ℕ∞) = Distribution.ofFun V f volume (⊤ : ℕ∞) :=
    Distribution.ofFun_congr_ae hFae
  have hUV : U ≤ V := subset_closure.trans hKUV
  have hvU := memHolderX_restrict_intrinsic driftWeight H.fields _ B U (hUV.trans hVB) 2 a hv
  obtain ⟨w, hw, hrep⟩ := distribution_representative_of_particular_solution_of_controlNorm G H C
    V U hK hKUV (by exact ha) (by exact_mod_cast ha1.le)
    (RothschildStein.S.distributionRestrictionCLM Ω V T) v (hvl.mono_set hVB) hvU
    (fun ψ => (hT.2 ψ).trans ((congrArg (fun Q : Distribution V ℝ (⊤ : ℕ∞) => Q ψ) hFF).symm.trans
      (heV.2 ψ).symm))
  refine ⟨w, hw, ?_⟩
  intro ψ
  have hh := hrep (TestFunction.monoCLM ℝ ψ)
  change T (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ ψ : TestFunction V ℝ (⊤ : ℕ∞))) = _ at hh
  rw [test_mono_comp Ω V U hVΩ hUV] at hh
  simpa [TestFunction.monoCLM_apply, hUV] using hh

end RothschildStein.H3

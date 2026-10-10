-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.WeakGradientGraph
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import RothschildStein.S.ClassicalWords
public import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.NormNum

/-!
# Closure of the smooth horizontal graph

Closing the linear span of smooth compactly supported function-gradient pairs inside the
Hilbert product gives a complete graph carrier. Weak derivative closedness shows that its
function projection remains injective.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- Function-gradient pairs represented by a smooth compactly supported function in the open
set. -/
def smoothGradientPairs : Set (GradientSpace U q) :=
  {v | ∃ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
    tsupport f ⊆ (U : Set (Fin N → ℝ)) ∧
    v.fst =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] f ∧
    ∀ i, v.snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      RothschildStein.fieldDerivative (X i) f}

/-- The linear span of the smooth function-gradient pairs. -/
def smoothGradientSpan : Submodule ℝ (GradientSpace U q) :=
  Submodule.span ℝ (smoothGradientPairs U X)

/-- The closure of the smooth horizontal graph, with the ambient Hilbert norm. -/
def energyGraph : Submodule ℝ (GradientSpace U q) := (smoothGradientSpan U X).topologicalClosure

/-- The smooth graph span is contained in its closure. -/
theorem smoothGradientSpan_le_energyGraph : smoothGradientSpan U X ≤ energyGraph U X :=
  Submodule.le_topologicalClosure _

/-- The energy graph is closed. -/
theorem isClosed_energyGraph : IsClosed (energyGraph U X : Set (GradientSpace U q)) :=
  Submodule.isClosed_topologicalClosure _

/-- The energy graph is a complete real inner product space. -/
instance : CompleteSpace (energyGraph U X) := (isClosed_energyGraph U X).completeSpace_coe

variable (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))

/-- Every smooth graph vector has the stated weak derivatives. -/
theorem smoothGradientSpan_le_weakGradientGraph :
    smoothGradientSpan U X ≤ weakGradientGraph U X hX := by
  apply Submodule.span_le.mpr
  rintro v ⟨f, hf, _, _, hvf, hvg⟩ i
  have hc := RothschildStein.S.hasWeakWordDeriv_classical U X hX [i] f hf.contDiffOn
  have hd : RothschildStein.wordDerivative X [i] f = RothschildStein.fieldDerivative (X i) f := rfl
  rw [hd] at hc
  exact RothschildStein.S.hasWeakWordDeriv_congr_ae X U hc hvf.symm (hvg i).symm

/-- Weak derivatives identify every vector in the closed smooth graph. -/
theorem energyGraph_le_weakGradientGraph : energyGraph U X ≤ weakGradientGraph U X hX := by
  exact Submodule.topologicalClosure_minimal _
    (smoothGradientSpan_le_weakGradientGraph U X hX) (isClosed_weakGradientGraph U X hX)

include hX in
/-- The closed smooth graph has no nonzero vertical vector, hence represents a single-valued
closed operator. -/
theorem energyGraph_fst_injective :
    Function.Injective (fun v : energyGraph U X => (v : GradientSpace U q).fst) := by
  intro v w h
  have he := weakGradientGraph_fst_injective U X hX
    (a₁ := ⟨v, energyGraph_le_weakGradientGraph U X hX v.property⟩)
    (a₂ := ⟨w, energyGraph_le_weakGradientGraph U X hX w.property⟩) h
  exact Subtype.ext (congrArg (fun z : weakGradientGraph U X hX => (z : GradientSpace U q)) he)

/-- The graph norm is the function norm together with the derivative norms. -/
theorem energyGraph_norm_sq (v : energyGraph U X) :
    ‖v‖ ^ 2 = ‖(v : GradientSpace U q).fst‖ ^ 2 +
      ∑ i, ‖(v : GradientSpace U q).snd i‖ ^ 2 := by
  change ‖(v : GradientSpace U q)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]

/-- A smooth compactly supported function has an L² gradient pair on the whole coordinate
space. -/
theorem exists_smoothGradientPair {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) :
    ∃ v ∈ smoothGradientPairs ⊤ X, v.fst =ᵐ[volume] f := by
  have hfp : MemLp f 2 (volume.restrict (⊤ : Opens (Fin N → ℝ))) :=
    hf.continuous.memLp_of_hasCompactSupport hc
  have hgp : ∀ i, MemLp (RothschildStein.fieldDerivative (X i) f) 2
      (volume.restrict (⊤ : Opens (Fin N → ℝ))) := by
    intro i
    have hd := RothschildStein.S.contDiffOn_fieldDerivative ⊤ (X i) f
      (hX i).contDiffOn hf.contDiffOn
    have hgc : HasCompactSupport (RothschildStein.fieldDerivative (X i) f) :=
      hc.of_isClosed_subset isClosed_closure (RothschildStein.S.tsupport_fieldDerivative_subset (X i) f)
    have hdg : ContDiff ℝ (⊤ : ℕ∞) (RothschildStein.fieldDerivative (X i) f) :=
      contDiffOn_univ.mp (by simpa only [Opens.coe_top] using hd)
    exact hdg.continuous.memLp_of_hasCompactSupport hgc
  let v : GradientSpace ⊤ q := WithLp.toLp 2 (hfp.toLp f,
    WithLp.toLp 2 (fun i => (hgp i).toLp (RothschildStein.fieldDerivative (X i) f)))
  refine ⟨v, ⟨f, hf, hc, subset_univ _, hfp.coeFn_toLp, fun i => (hgp i).coeFn_toLp⟩, ?_⟩
  simpa only [v, WithLp.toLp_fst, Opens.coe_top, Measure.restrict_univ] using hfp.coeFn_toLp

/-- The function projection of the closed smooth graph is densely defined. -/
theorem denseRange_energyGraph_fst (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) :
    DenseRange (fun v : energyGraph ⊤ X => (v : GradientSpace (N := N) ⊤ q).fst) := by
  have hd := Lp.dense_hasCompactSupport_contDiff (E := Fin N → ℝ) (F := ℝ)
    (μ := volume.restrict (⊤ : Opens (Fin N → ℝ))) (p := 2) (by norm_num)
  apply hd.mono
  rintro u ⟨f, huf, hc, hf⟩
  obtain ⟨v, hv, hvf⟩ := exists_smoothGradientPair X hf hc hX
  refine ⟨⟨v, smoothGradientSpan_le_energyGraph ⊤ X (Submodule.subset_span hv)⟩, ?_⟩
  apply Lp.ext
  have huf' : (u : (Fin N → ℝ) → ℝ) =ᵐ[volume] f := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using huf
  simpa only [Opens.coe_top, Measure.restrict_univ] using hvf.trans huf'.symm

end HeatKernel

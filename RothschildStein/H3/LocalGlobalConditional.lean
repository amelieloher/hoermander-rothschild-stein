-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ActualConvolutionConditional
public import RothschildStein.H3.ConvolutionGlobalSecond
public import RothschildStein.H3.QuasiballOriginFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
open G2

/-- Local Sobolev solvability on every origin quasiball,
with the same actual convolution and certified forcing representative. -/
def ConvolutionLocalSolutions {n q : ℕ} (G : HomogeneousGroup n)
    (H : H1.StandingHypotheses G q) (ν : HomogeneousNorm G)
    (p : ℝ≥0∞) (F K : (Fin n → ℝ) → ℝ)
    (C : ℝ → List (Fin (q+1)) → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    memSobolevX driftWeight H.fields (quasiballDomain G ν 0 R) 2 p (groupConvolution G F K) ∧
      ∃ D : WeakDriftOperatorData H.fields (quasiballDomain G ν 0 R) p (groupConvolution G F K),
        D.operator =ᵐ[volume.restrict (quasiballDomain G ν 0 R : Set (Fin n → ℝ))] F ∧
        ∀ I ∈ wordFamily driftWeight 2,
          weakWordENorm H.fields (quasiballDomain G ν 0 R) I p (groupConvolution G F K) ≤
            ENNReal.ofReal (C R I)*eLpNorm F p volume

end RothschildStein.H3

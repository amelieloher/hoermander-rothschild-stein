-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Hormander.Interface.BasisVec

public import RothschildStein.Definitions.polynomialProduct
public import RothschildStein.Definitions.coordinateDilation
public import RothschildStein.Definitions.HomogeneousGroup
public import RothschildStein.Definitions.HomogeneousGroup.mul
public import RothschildStein.Definitions.HomogeneousGroup.inv
public import RothschildStein.Definitions.HomogeneousGroup.dilate
public import RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension
public import RothschildStein.Definitions.HomogeneousGroup.canonicalField
public import RothschildStein.Definitions.euclideanPartial
public import RothschildStein.Definitions.SmoothDifferentialOperator
public import RothschildStein.Definitions.SmoothDifferentialOperator.apply
public import RothschildStein.Definitions.SmoothDifferentialOperator.IsHomogeneous
public import RothschildStein.Definitions.HomogeneousGroup.IsHomogeneousGauge
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields
public import RothschildStein.Definitions.HomogeneousGroup.driftFields
public import RothschildStein.Definitions.HomogeneousGroup.HasHomogeneousDistribution
public import RothschildStein.Definitions.isFundamentalDistribution
public import RothschildStein.Definitions.HomogeneousGroup.potential
public import RothschildStein.Definitions.HomogeneousGroup.HasPrincipalValue
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.representsDistribution
public import RothschildStein.Definitions.fieldDerivative
public import RothschildStein.Definitions.sumSquares
public import RothschildStein.Definitions.sumSquaresTranspose
public import RothschildStein.Definitions.sumSquaresWithDrift
public import RothschildStein.Definitions.sumSquaresWithDriftTranspose
public import RothschildStein.Provider.rs2a_noDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein

theorem rs2a_noDrift
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (ν : (Fin N → ℝ) → ℝ) (hν : G.IsHomogeneousGauge ν) :
    let X := G.horizontalFields hq
    let Y := X
    let L := sumSquares X
    let Lt := sumSquaresTranspose X
    ∃ Γ Γstar : (Fin N → ℝ) → ℝ,
      (∀ x, Γstar x = Γ (G.inv x)) ∧
    (∀ x, Γstar x = Γ x) ∧
      ((∀ x, G.inv x = -x) → ∀ x, Γstar x = Γ (-x)) ∧
      ∃ a : Bool → Fin q → Fin q → ℝ, ∀ b : Bool,
        let K := if b then Γstar else Γ
        let P := if b then Lt else L
        let Pt := if b then L else Lt
        ∃ T : Distribution (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
          G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ)) T ∧
          isFundamentalDistribution Pt T ∧
          (∀ S : Distribution (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
            G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ)) S →
            isFundamentalDistribution Pt S → S = T) ∧
          representsDistribution ⊤ T K ∧
          ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ) ∧
          (∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
            K (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * K x) ∧
          (∃ C : ℝ, 0 < C ∧ ∀ x : Fin N → ℝ, x ≠ 0 →
            |K x| ≤ C * ν x ^ (2 - (G.homogeneousDimension : ℝ)) ∧
            (∀ i : Fin q, |fieldDerivative (Y i) K x| ≤
              C * ν x ^ (1 - (G.homogeneousDimension : ℝ))) ∧
            (∀ i j : Fin q,
              |fieldDerivative (Y i) (fieldDerivative (Y j) K) x| ≤
                C * ν x ^ (-(G.homogeneousDimension : ℝ)))) ∧
          (∀ (D : SmoothDifferentialOperator N) (k : ℝ), D.IsHomogeneous G k →
            ∃ C : ℝ, 0 < C ∧ ∀ x : Fin N → ℝ, x ≠ 0 →
              |D.apply K x| ≤ C * ν x ^ (2 - (G.homogeneousDimension : ℝ) - k)) ∧
          (∀ (D : SmoothDifferentialOperator N), D.IsHomogeneous G 2 →
            ∀ r R : ℝ, 0 < r → r < R →
            ∀ Φ : ℝ → ℝ, ContinuousOn Φ (Icc r R) →
              IntegrableOn (fun x => D.apply K x * Φ (ν x)) {x | r < ν x ∧ ν x < R} ∧
              (∫ x in {x | r < ν x ∧ ν x < R}, D.apply K x * Φ (ν x)) = 0) ∧
          (∀ φ : TestFunction (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
            ContDiff ℝ (⊤ : ℕ∞) (G.potential K φ) ∧
            (∀ v, P (G.potential K φ) v = φ v) ∧
            ∀ v : Fin N → ℝ,
              Integrable (fun u => P φ u * K (G.mul (G.inv u) v)) ∧
              φ v = G.potential K (P φ) v ∧
              (∀ j : Fin q,
                Integrable (fun u => P φ u * fieldDerivative (Y j) K (G.mul (G.inv u) v)) ∧
                fieldDerivative (Y j) φ v = G.potential (fieldDerivative (Y j) K) (P φ) v) ∧
              (∀ i j : Fin q,
                G.HasPrincipalValue ν (fieldDerivative (Y i) (fieldDerivative (Y j) K))
                  (P φ) v (fieldDerivative (Y i) (fieldDerivative (Y j) φ) v - a b i j * P φ v))) :=
  by exact RothschildStein.Provider.rs2a_noDrift G hq hqpos hw hQ hspan ν hν

end RothschildStein

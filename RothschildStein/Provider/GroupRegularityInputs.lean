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
public import RothschildStein.Definitions.noDriftWeight
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Definitions.controlDistance
public import RothschildStein.Definitions.wordFamily
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.memSobolevX
public import RothschildStein.Definitions.weakWordENorm
public import RothschildStein.Definitions.sobolevXENorm
public import RothschildStein.Definitions.memHolderXCompact
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.memHolderXLoc
public import RothschildStein.Definitions.memSobolevXLoc
public import RothschildStein.Definitions.hasIntrinsicWordDeriv
public import RothschildStein.Definitions.holderSeminorm
public import RothschildStein.Definitions.holderENorm
public import RothschildStein.Definitions.intrinsicWordENorm
public import RothschildStein.Definitions.holderXENorm
public import RothschildStein.Definitions.representsDistribution
public import RothschildStein.Definitions.hasDistributionEquation
public import RothschildStein.Definitions.hasDistributionEquationWithDrift
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff
public import RothschildStein.Definitions.HomogeneousGroup.driftFields_contDiff


set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein.Provider
variable {N m : ℕ}

/-- A distributional equation, passed as a parameter: for an open set, a distribution and a
right-hand side, the proposition that the distribution solves the equation there. -/
abbrev DistributionalEquation (N : ℕ) :=
  ∀ Ω : Opens (Fin N → ℝ), Distribution Ω ℝ (⊤ : ℕ∞) → ((Fin N → ℝ) → ℝ) → Prop

/-- Global Lp regularity, principal and horizontal first derivative bounds,
and the full norm
(BB Thm 8.27, pp. 360–362; repaired exhaustion route). -/
def GlobalLpRegularity (_G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (E : DistributionalEquation N) (_νs : (Fin N → ℝ) → ℝ) : Prop :=
    let H := (wordFamily w 2).filter (fun I => wordWeight w I = 1)
    let B := (wordFamily w 2).filter (fun I => wordWeight w I = 2)
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∃ C : ℝ, 0 < C ∧
      ∀ u f : (Fin N → ℝ) → ℝ,
        MemLp u p volume → MemLp f p volume →
        (∃ T : Distribution (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
          representsDistribution ⊤ T u ∧
          E ⊤ T f) →
        memSobolevX w X ⊤ 2 p u ∧
        (∑ I ∈ B, weakWordENorm X ⊤ I p u) ≤ ENNReal.ofReal C * eLpNorm f p volume ∧
        sobolevXENorm w X ⊤ 2 p u ≤ ENNReal.ofReal C *
          (eLpNorm f p volume + eLpNorm u p volume) ∧
        (∑ I ∈ H, weakWordENorm X ⊤ I p u) ≤ ENNReal.ofReal C *
          (eLpNorm f p volume + eLpNorm u p volume))

/-- Both compact Hölder estimates: full norm with support-radius
dependence and the global seminorm bound (BB pp. 379–380). -/
def CompactHolderEstimates (_G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (E : DistributionalEquation N) (_νs : (Fin N → ℝ) → ℝ) : Prop :=
    let d := controlDistance univ w X
    let B := (wordFamily w 2).filter (fun I => wordWeight w I = 2)
    (∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ u : (Fin N → ℝ) → ℝ, memHolderXCompact w X d ⊤ 2 α u →
        ∃ f : (Fin N → ℝ) → ℝ,
          memHolderX w X d ⊤ 0 α f ∧
          E ⊤
            (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) f ∧
        ∃ g : List (Fin m) → (Fin N → ℝ) → ℝ,
          (∀ I ∈ B, hasIntrinsicWordDeriv X ⊤ I u (g I)) ∧
          (∑ I ∈ B, holderSeminorm d α univ (g I)) ≤
            ENNReal.ofReal C * holderSeminorm d α univ f)
    ∧ (∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ,
      ∀ u : (Fin N → ℝ) → ℝ, memHolderXCompact w X d ⊤ 2 α u →
        tsupport u ⊆ {x | d z x < ENNReal.ofReal R} →
        ∃ f : (Fin N → ℝ) → ℝ,
          memHolderX w X d ⊤ 0 α f ∧
          E ⊤
            (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) f ∧
          (∑ I ∈ B, intrinsicWordENorm X d ⊤ I α u) ≤
            ENNReal.ofReal C * holderENorm d α univ f)

/-- Distributional local Lp regularity and the full
interior estimate, including the F.glue representative bridge (BB pp. 374–375). -/
def LocalLpRegularity (_G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (E : DistributionalEquation N) (_νs : (Fin N → ℝ) → ℝ) : Prop :=
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ →
      ∀ Ω : TopologicalSpace.Opens (Fin N → ℝ),
      ∀ T : Distribution Ω ℝ (⊤ : ℕ∞), ∀ f : (Fin N → ℝ) → ℝ,
        memSobolevXLoc w X Ω 0 p f →
        E Ω T f →
        ∃ u : (Fin N → ℝ) → ℝ, representsDistribution Ω T u ∧
          memSobolevXLoc w X Ω 2 p u)
    ∧ (∀ p : ℝ≥0∞, 1 < p → p < ⊤ →
      ∀ Ω A V : TopologicalSpace.Opens (Fin N → ℝ),
        IsCompact (closure (A : Set (Fin N → ℝ))) →
        closure (A : Set (Fin N → ℝ)) ⊆ (V : Set (Fin N → ℝ)) →
        IsCompact (closure (V : Set (Fin N → ℝ))) →
        closure (V : Set (Fin N → ℝ)) ⊆ (Ω : Set (Fin N → ℝ)) →
      ∃ C : ℝ, 0 < C ∧ ∀ u f : (Fin N → ℝ) → ℝ,
        memSobolevXLoc w X Ω 2 p u →
        E Ω
          (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f →
        MemLp f p (volume.restrict (V : Set (Fin N → ℝ))) →
        sobolevXENorm w X A 2 p u ≤ ENNReal.ofReal C *
          (eLpNorm f p (volume.restrict (V : Set (Fin N → ℝ))) +
           eLpNorm u p (volume.restrict (V : Set (Fin N → ℝ)))))

/-- Distributional local Hölder regularity and its full interior
estimate, including the F.glue representative bridge (BB p. 389). -/
def LocalHolderRegularity (_G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (E : DistributionalEquation N) (_νs : (Fin N → ℝ) → ℝ) : Prop :=
    let d := controlDistance univ w X
    (∀ α : ℝ, 0 < α → α < 1 →
      ∀ Ω : TopologicalSpace.Opens (Fin N → ℝ),
      ∀ T : Distribution Ω ℝ (⊤ : ℕ∞), ∀ f : (Fin N → ℝ) → ℝ,
        memHolderXLoc w X d Ω 0 α f →
        E Ω T f →
        ∃ u : (Fin N → ℝ) → ℝ, representsDistribution Ω T u ∧
          memHolderXLoc w X d Ω 2 α u)
    ∧ (∀ α : ℝ, 0 < α → α < 1 →
      ∀ Ω A V : TopologicalSpace.Opens (Fin N → ℝ),
        IsCompact (closure (A : Set (Fin N → ℝ))) →
        closure (A : Set (Fin N → ℝ)) ⊆ (V : Set (Fin N → ℝ)) →
        IsCompact (closure (V : Set (Fin N → ℝ))) →
        closure (V : Set (Fin N → ℝ)) ⊆ (Ω : Set (Fin N → ℝ)) →
      ∃ C : ℝ, 0 < C ∧ ∀ u f : (Fin N → ℝ) → ℝ,
        memHolderXLoc w X d Ω 2 α u →
        E Ω
          (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f →
        holderENorm d α (V : Set (Fin N → ℝ)) f < ⊤ →
        holderXENorm w X d A 2 α u ≤ ENNReal.ofReal C *
          (holderENorm d α (V : Set (Fin N → ℝ)) f +
            ⨆ x : V, ENNReal.ofReal |u x|))

/-- Lp solvability on domains contained in a control ball,
with the radius-dependent bound (BB Thm 8.5, p. 340). -/
def BallLpSolvability (_G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (E : DistributionalEquation N) (_νs : (Fin N → ℝ) → ℝ) : Prop :=
    let d := controlDistance univ w X
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, 0 < C ∧ ∀ Ω : TopologicalSpace.Opens (Fin N → ℝ),
        (Ω : Set (Fin N → ℝ)) ⊆ {x | d 0 x < ENNReal.ofReal R} →
      ∀ f : (Fin N → ℝ) → ℝ, MemLp f p (volume.restrict (Ω : Set (Fin N → ℝ))) →
        ∃ u : (Fin N → ℝ) → ℝ, memSobolevX w X Ω 2 p u ∧
          E Ω
            (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f ∧
          sobolevXENorm w X Ω 2 p u ≤ ENNReal.ofReal C *
            eLpNorm f p (volume.restrict (Ω : Set (Fin N → ℝ))))

/-- The covering estimate transferring the scale-invariant local `W^{2,p}` estimate
(BB Thm 8.44) to the balls of an arbitrary smooth inverse-symmetric gauge `νs`.
This is a separate hypothesis; the estimate for a single fixed gauge alone is insufficient. -/
def QuasiballLpTransfer (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (E : DistributionalEquation N) (νs : (Fin N → ℝ) → ℝ) : Prop :=
    let H := (wordFamily w 2).filter (fun I => wordWeight w I = 1)
    let B := (wordFamily w 2).filter (fun I => wordWeight w I = 2)
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∃ C : ℝ, 0 < C ∧
      ∀ z : Fin N → ℝ, ∀ r : ℝ, 0 < r →
      ∀ U V : TopologicalSpace.Opens (Fin N → ℝ),
        (∀ x, x ∈ U ↔ νs (G.mul (G.inv z) x) < r) →
        (∀ x, x ∈ V ↔ νs (G.mul (G.inv z) x) < r / 2) →
      ∀ u : (Fin N → ℝ) → ℝ, memSobolevX w X U 2 p u →
        ∃ f : (Fin N → ℝ) → ℝ,
          MemLp f p (volume.restrict (U : Set (Fin N → ℝ))) ∧
          E U
            (Distribution.ofFun U u volume (⊤ : ℕ∞)) f ∧
          (∑ I ∈ B, weakWordENorm X V I p u) +
            ENNReal.ofReal (r⁻¹) * (∑ I ∈ H, weakWordENorm X V I p u) +
            ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (V : Set (Fin N → ℝ))) ≤
          ENNReal.ofReal C * (eLpNorm f p (volume.restrict (U : Set (Fin N → ℝ))) +
            ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (U : Set (Fin N → ℝ)))))

/-- Hölder solvability in `C^{2,α}` transferred from gauge balls to control-distance balls,
for a solution on a larger gauge ball (BB Prop 8.58, pp. 386–387). -/
def HolderBallTransfer (_G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (E : DistributionalEquation N) (νs : (Fin N → ℝ) → ℝ) : Prop :=
    let d := controlDistance univ w X
    (∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ, 0 < R →
      ∃ S : ℝ, R < S ∧ ∃ V : TopologicalSpace.Opens (Fin N → ℝ),
        (∀ x, x ∈ V ↔ νs x < S) ∧
        {x | d 0 x < ENNReal.ofReal R} ⊆ (V : Set (Fin N → ℝ)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ Ω : TopologicalSpace.Opens (Fin N → ℝ),
        (Ω : Set (Fin N → ℝ)) ⊆ {x | d 0 x < ENNReal.ofReal R} →
      ∀ f : (Fin N → ℝ) → ℝ, memHolderXCompact w X d Ω 0 α f →
        (∀ x ∉ Ω, f x = 0) →
        ∃ u : (Fin N → ℝ) → ℝ, memHolderX w X d V 2 α u ∧
          E V
            (Distribution.ofFun V u volume (⊤ : ℕ∞)) f ∧
          holderXENorm w X d V 2 α u ≤ ENNReal.ofReal C * holderENorm d α univ f)

/-- The inputs for the regularity theorem on a homogeneous group. No field
assumes the full theorem. The analytic estimates and the two geometric
gauge-transfer statements are separate fields, so that each can be proved independently. -/
structure GroupRegularityInputs (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (E : DistributionalEquation N) (νs : (Fin N → ℝ) → ℝ) : Prop where
  globalLp : GlobalLpRegularity G w X E νs
  compactHolder : CompactHolderEstimates G w X E νs
  localLp : LocalLpRegularity G w X E νs
  localHolder : LocalHolderRegularity G w X E νs
  lpSolve : BallLpSolvability G w X E νs
  quasiball : QuasiballLpTransfer G w X E νs
  holderBall : HolderBallTransfer G w X E νs


/-- The regularity properties required for canonical no-drift systems.
Each field records a regularity statement for the given data. -/
structure CanonicalNoDriftRegularity : Prop where
  globalLp : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    GlobalLpRegularity G noDriftWeight (G.horizontalFields hq)
      (fun Ω => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)) νs
  compactHolder : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    CompactHolderEstimates G noDriftWeight (G.horizontalFields hq)
      (fun Ω => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)) νs
  localLp : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    LocalLpRegularity G noDriftWeight (G.horizontalFields hq)
      (fun Ω => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)) νs
  localHolder : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    LocalHolderRegularity G noDriftWeight (G.horizontalFields hq)
      (fun Ω => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)) νs
  lpSolve : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    BallLpSolvability G noDriftWeight (G.horizontalFields hq)
      (fun Ω => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)) νs
  quasiball : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    QuasiballLpTransfer G noDriftWeight (G.horizontalFields hq)
      (fun Ω => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)) νs
  holderBall : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    HolderBallTransfer G noDriftWeight (G.horizontalFields hq)
      (fun Ω => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)) νs

/-- Instantiate the independent inputs for one canonical system. -/
theorem CanonicalNoDriftRegularity.forSystem (U : CanonicalNoDriftRegularity)
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (hνs_symm : ∀ x, νs (G.inv x) = νs x) :
    GroupRegularityInputs G noDriftWeight (G.horizontalFields hq)
      (fun Ω => hasDistributionEquation Ω (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn)) νs :=
  ⟨U.globalLp G hq hqpos hw hQ hspan νs hνs hνs_smooth hνs_symm,
    U.compactHolder G hq hqpos hw hQ hspan νs hνs hνs_smooth hνs_symm,
    U.localLp G hq hqpos hw hQ hspan νs hνs hνs_smooth hνs_symm,
    U.localHolder G hq hqpos hw hQ hspan νs hνs hνs_smooth hνs_symm,
    U.lpSolve G hq hqpos hw hQ hspan νs hνs hνs_smooth hνs_symm,
    U.quasiball G hq hqpos hw hQ hspan νs hνs hνs_smooth hνs_symm,
    U.holderBall G hq hqpos hw hQ hspan νs hνs hνs_smooth hνs_symm⟩

/-- The regularity properties required for canonical drift systems.
Each field records a regularity statement for the given data. -/
structure CanonicalDriftRegularity : Prop where
  globalLp : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (_hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    GlobalLpRegularity G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs
  compactHolder : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (_hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    CompactHolderEstimates G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs
  localLp : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (_hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    LocalLpRegularity G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs
  localHolder : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (_hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    LocalHolderRegularity G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs
  lpSolve : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (_hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    BallLpSolvability G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs
  quasiball : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (_hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    QuasiballLpTransfer G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs
  holderBall : ∀
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (_hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (_hQ : 3 ≤ G.homogeneousDimension)
    (_hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (_hνs : G.IsHomogeneousGauge νs)
    (_hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (_hνs_symm : ∀ x, νs (G.inv x) = νs x),
    HolderBallTransfer G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs

/-- Instantiate the independent inputs for one canonical system. -/
theorem CanonicalDriftRegularity.forSystem (U : CanonicalDriftRegularity)
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (hνs_symm : ∀ x, νs (G.inv x) = νs x) :
    GroupRegularityInputs G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs :=
  ⟨U.globalLp G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm,
    U.compactHolder G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm,
    U.localLp G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm,
    U.localHolder G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm,
    U.lpSolve G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm,
    U.quasiball G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm,
    U.holderBall G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm⟩

end RothschildStein.Provider

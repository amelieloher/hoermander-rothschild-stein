-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Provider.GroupRegularityDrift
public import RothschildStein.Provider.CanonicalDriftRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein.Provider

/-- Global and local `W^{2,p}` and `C^{2,α}` estimates for the drift operator on a homogeneous group
(BB Chapter 8), with every input proved. -/
theorem rs2b_drift
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (hνs_symm : ∀ x, νs (G.inv x) = νs x)
    :
    let X := G.driftFields hq
    let w := driftWeight
    let d := controlDistance univ w X
    let H := (wordFamily w 2).filter (fun I => wordWeight w I = 1)
    let B := (wordFamily w 2).filter (fun I => wordWeight w I = 2)
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∃ C : ℝ, 0 < C ∧
      ∀ u f : (Fin N → ℝ) → ℝ,
        MemLp u p volume → MemLp f p volume →
        (∃ T : Distribution (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
          representsDistribution ⊤ T u ∧
          hasDistributionEquationWithDrift ⊤ X (fun i => (G.driftFields_contDiff hq i).contDiffOn) T f) →
        memSobolevX w X ⊤ 2 p u ∧
        (∑ I ∈ B, weakWordENorm X ⊤ I p u) ≤ ENNReal.ofReal C * eLpNorm f p volume ∧
        sobolevXENorm w X ⊤ 2 p u ≤ ENNReal.ofReal C *
          (eLpNorm f p volume + eLpNorm u p volume)) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ u : (Fin N → ℝ) → ℝ, memHolderXCompact w X d ⊤ 2 α u →
        ∃ f : (Fin N → ℝ) → ℝ,
          memHolderX w X d ⊤ 0 α f ∧
          hasDistributionEquationWithDrift ⊤ X (fun i => (G.driftFields_contDiff hq i).contDiffOn)
            (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) f ∧
        ∃ g : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
          (∀ I ∈ B, hasIntrinsicWordDeriv X ⊤ I u (g I)) ∧
          (∑ I ∈ B, holderSeminorm d α univ (g I)) ≤
            ENNReal.ofReal C * holderSeminorm d α univ f) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ,
      ∀ u : (Fin N → ℝ) → ℝ, memHolderXCompact w X d ⊤ 2 α u →
        tsupport u ⊆ {x | d z x < ENNReal.ofReal R} →
        ∃ f : (Fin N → ℝ) → ℝ,
          memHolderX w X d ⊤ 0 α f ∧
          hasDistributionEquationWithDrift ⊤ X (fun i => (G.driftFields_contDiff hq i).contDiffOn)
            (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) f ∧
          (∑ I ∈ B, intrinsicWordENorm X d ⊤ I α u) ≤
            ENNReal.ofReal C * holderENorm d α univ f) ∧
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∃ C : ℝ, 0 < C ∧
      ∀ z : Fin N → ℝ, ∀ r : ℝ, 0 < r →
      ∀ U V : TopologicalSpace.Opens (Fin N → ℝ),
        (∀ x, x ∈ U ↔ νs (G.mul (G.inv z) x) < r) →
        (∀ x, x ∈ V ↔ νs (G.mul (G.inv z) x) < r / 2) →
      ∀ u : (Fin N → ℝ) → ℝ, memSobolevX w X U 2 p u →
        ∃ f : (Fin N → ℝ) → ℝ,
          MemLp f p (volume.restrict (U : Set (Fin N → ℝ))) ∧
          hasDistributionEquationWithDrift U X (fun i => (G.driftFields_contDiff hq i).contDiffOn)
            (Distribution.ofFun U u volume (⊤ : ℕ∞)) f ∧
          (∑ I ∈ B, weakWordENorm X V I p u) +
            ENNReal.ofReal (r⁻¹) * (∑ I ∈ H, weakWordENorm X V I p u) +
            ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (V : Set (Fin N → ℝ))) ≤
          ENNReal.ofReal C * (eLpNorm f p (volume.restrict (U : Set (Fin N → ℝ))) +
            ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (U : Set (Fin N → ℝ))))) ∧
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ →
      ∀ Ω : TopologicalSpace.Opens (Fin N → ℝ),
      ∀ T : Distribution Ω ℝ (⊤ : ℕ∞), ∀ f : (Fin N → ℝ) → ℝ,
        memSobolevXLoc w X Ω 0 p f →
        hasDistributionEquationWithDrift Ω X (fun i => (G.driftFields_contDiff hq i).contDiffOn) T f →
        ∃ u : (Fin N → ℝ) → ℝ, representsDistribution Ω T u ∧
          memSobolevXLoc w X Ω 2 p u) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      ∀ Ω : TopologicalSpace.Opens (Fin N → ℝ),
      ∀ T : Distribution Ω ℝ (⊤ : ℕ∞), ∀ f : (Fin N → ℝ) → ℝ,
        memHolderXLoc w X d Ω 0 α f →
        hasDistributionEquationWithDrift Ω X (fun i => (G.driftFields_contDiff hq i).contDiffOn) T f →
        ∃ u : (Fin N → ℝ) → ℝ, representsDistribution Ω T u ∧
          memHolderXLoc w X d Ω 2 α u) ∧
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ →
      ∀ Ω A V : TopologicalSpace.Opens (Fin N → ℝ),
        IsCompact (closure (A : Set (Fin N → ℝ))) →
        closure (A : Set (Fin N → ℝ)) ⊆ (V : Set (Fin N → ℝ)) →
        IsCompact (closure (V : Set (Fin N → ℝ))) →
        closure (V : Set (Fin N → ℝ)) ⊆ (Ω : Set (Fin N → ℝ)) →
      ∃ C : ℝ, 0 < C ∧ ∀ u f : (Fin N → ℝ) → ℝ,
        memSobolevXLoc w X Ω 2 p u →
        hasDistributionEquationWithDrift Ω X (fun i => (G.driftFields_contDiff hq i).contDiffOn)
          (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f →
        MemLp f p (volume.restrict (V : Set (Fin N → ℝ))) →
        sobolevXENorm w X A 2 p u ≤ ENNReal.ofReal C *
          (eLpNorm f p (volume.restrict (V : Set (Fin N → ℝ))) +
           eLpNorm u p (volume.restrict (V : Set (Fin N → ℝ))))) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      ∀ Ω A V : TopologicalSpace.Opens (Fin N → ℝ),
        IsCompact (closure (A : Set (Fin N → ℝ))) →
        closure (A : Set (Fin N → ℝ)) ⊆ (V : Set (Fin N → ℝ)) →
        IsCompact (closure (V : Set (Fin N → ℝ))) →
        closure (V : Set (Fin N → ℝ)) ⊆ (Ω : Set (Fin N → ℝ)) →
      ∃ C : ℝ, 0 < C ∧ ∀ u f : (Fin N → ℝ) → ℝ,
        memHolderXLoc w X d Ω 2 α u →
        hasDistributionEquationWithDrift Ω X (fun i => (G.driftFields_contDiff hq i).contDiffOn)
          (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f →
        holderENorm d α (V : Set (Fin N → ℝ)) f < ⊤ →
        holderXENorm w X d A 2 α u ≤ ENNReal.ofReal C *
          (holderENorm d α (V : Set (Fin N → ℝ)) f +
            ⨆ x : V, ENNReal.ofReal |u x|)) ∧
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, 0 < C ∧ ∀ Ω : TopologicalSpace.Opens (Fin N → ℝ),
        (Ω : Set (Fin N → ℝ)) ⊆ {x | d 0 x < ENNReal.ofReal R} →
      ∀ f : (Fin N → ℝ) → ℝ, MemLp f p (volume.restrict (Ω : Set (Fin N → ℝ))) →
        ∃ u : (Fin N → ℝ) → ℝ, memSobolevX w X Ω 2 p u ∧
          hasDistributionEquationWithDrift Ω X (fun i => (G.driftFields_contDiff hq i).contDiffOn)
            (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f ∧
          sobolevXENorm w X Ω 2 p u ≤ ENNReal.ofReal C *
            eLpNorm f p (volume.restrict (Ω : Set (Fin N → ℝ)))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ, 0 < R →
      ∃ S : ℝ, R < S ∧ ∃ V : TopologicalSpace.Opens (Fin N → ℝ),
        (∀ x, x ∈ V ↔ νs x < S) ∧
        {x | d 0 x < ENNReal.ofReal R} ⊆ (V : Set (Fin N → ℝ)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ Ω : TopologicalSpace.Opens (Fin N → ℝ),
        (Ω : Set (Fin N → ℝ)) ⊆ {x | d 0 x < ENNReal.ofReal R} →
      ∀ f : (Fin N → ℝ) → ℝ, memHolderXCompact w X d Ω 0 α f →
        (∀ x ∉ Ω, f x = 0) →
        ∃ u : (Fin N → ℝ) → ℝ, memHolderX w X d V 2 α u ∧
          hasDistributionEquationWithDrift V X (fun i => (G.driftFields_contDiff hq i).contDiffOn)
            (Distribution.ofFun V u volume (⊤ : ℕ∞)) f ∧
          holderXENorm w X d V 2 α u ≤ ENNReal.ofReal C * holderENorm d α univ f) := by
  exact rs2b_drift_of_regularityInputs G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm canonicalDriftRegularity_holds



end RothschildStein.Provider

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalizedFirstHolderEstimate
public import RothschildStein.H3.LocalizedHolderSourceNorm
public import RothschildStein.H3.CutoffProductNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- Actual local fixed inputs obey the cutoff coefficient
estimate used for iteration. The compact source supremum is eliminated
using the constructed local jets and shared drift cutoff estimates. -/
theorem localized_first_coefficient_estimate_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ,
      ∀ U V : Opens (Fin N → ℝ),
      (U : Set (Fin N → ℝ)) ⊆ G2.gaugeBall G Hc.norm z ρ →
      ∀ u : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        U 2 (α : ℝ) u →
      ∀ φ : TestFunction U ℝ (⊤ : ℕ∞), EqOn φ 1 (V : Set (Fin N → ℝ)) →
      ∀ A B : ℝ≥0∞,
      eLpNorm φ ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ≤ 1 →
      (∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤
        (volume.restrict (U : Set (Fin N → ℝ))) ≤ A) →
      eLpNorm (sumSquaresWithDrift H.fields φ) ⊤
        (volume.restrict (U : Set (Fin N → ℝ))) ≤ B →
      ∃ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
        jet [] = u ∧
        (∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv H.fields U I u (jet I) ∧
          holderENorm (controlDistance univ driftWeight H.fields) (α : ℝ)
            (U : Set (Fin N → ℝ)) (jet I) < ⊤) ∧
        ∀ η : ℝ, 0 < η → η < 1 →
        holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
          V 1 (α : ℝ) u ≤
          ENNReal.ofReal η *
            (eLpNorm (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) ⊤
              (volume.restrict (U : Set (Fin N → ℝ))) +
             B * eLpNorm u ⊤ (volume.restrict (U : Set (Fin N → ℝ))) +
             2 * A * holderXENorm driftWeight H.fields
               (controlDistance univ driftWeight H.fields) U 1 (α : ℝ) u) +
          ENNReal.ofReal (C * η ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) /
            (1 - (α : ℝ))))) * eLpNorm u ⊤ (volume.restrict (U : Set (Fin N → ℝ))) := by
  obtain ⟨C, hC, hb⟩ := localized_first_holder_estimate_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hρ
  let D := S.groupControlGeometry_of_controlNorm G driftWeight H.fields Hc ⊤
  refine ⟨C, hC, ?_⟩
  intro z U V hU u hu φ hφ A B hn hA hB
  obtain ⟨jet, hzero, hj, hbound⟩ := hb z U V hU u hu φ hφ
  obtain ⟨hJ0, hJ⟩ := cutoff_continuous_intrinsic_jets U driftWeight H.fields
    (H.fields_smooth G) 2 u jet hzero (fun I hI => (hj I hI).1)
    (fun I hI => S.continuousOn_of_holderENorm_lt_top_subset ⊤ D
      (subset_univ _) (show 0 < (α : ℝ) from hα) (hj I hI).2) φ
  let J := fun I => S.leibnizWordValue H.fields I jet φ
  have hdata := intrinsicJetSource_data J (fun I hI => (hJ I hI).2.1)
    (fun I hI => (hJ I hI).2.2.1) (fun I hI => (hJ I hI).2.2.2)
  have hw : MemLp (fun x => u x * φ x) ⊤ volume := by
    have hnil := hJ [] (by simp [wordWeight])
    rw [← hJ0]
    exact hnil.2.1.memLp_of_hasCompactSupport hnil.2.2.1
  have hs := localized_holder_source_norm_le ⊤ U D (subset_univ _) H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) (show 0 < (α : ℝ) from hα)
    u jet hzero hj φ A B hn hA hB
  have hwbound := cutoff_product_global_norm_le U ⊤ (by simp) u φ hn
  refine ⟨jet, hzero, hj, ?_⟩
  intro η hη hη1
  have hh := hbound η hη hη1
  dsimp only at hh
  rw [ENNReal.ofReal_mul hη.le, ofReal_lpNorm
    (hdata.1.memLp_of_hasCompactSupport hdata.2.1),
    ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg hη.le _)), ofReal_lpNorm hw] at hh
  exact hh.trans (add_le_add (mul_le_mul' le_rfl hs) (mul_le_mul' le_rfl hwbound))

end RothschildStein.H3

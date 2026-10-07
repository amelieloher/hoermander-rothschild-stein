-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactGlobalHolderIntrinsicJets
public import RothschildStein.P2.HolderTransfer
public import RothschildStein.S.HolderBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- A compact gauge-Hölder function has finite control-distance norm,
using the identification of the control distance with the gauge metric. -/
theorem holderENorm_finite_of_compact_gauge_holder {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X) {α : ℝ} (hα : 0 ≤ α)
    {f : (Fin N → ℝ) → ℝ} (hc : Continuous f) (hs : HasCompactSupport f)
    {A : ℝ} (hh : ∀ x y, |f x - f y| ≤ A * G2.gaugeDistance G C.norm x y ^ α) :
    holderENorm (controlDistance univ w X) α univ f < ⊤ := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hc
  have hsup : (⨆ x : (univ : Set (Fin N → ℝ)), ENNReal.ofReal |f x|) ≤
      ENNReal.ofReal M := by
    apply iSup_le
    intro x
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hM x)
  have hsemi : holderSeminorm (controlDistance univ w X) α univ f ≤ ENNReal.ofReal |A| := by
    apply S.holderSeminorm_le_of_bound _ _ _ _ _ ENNReal.ofReal_lt_top
    intro x _ y _ _
    have hn : 0 ≤ G2.gaugeDistance G C.norm x y := C.norm.gauge.2.1 _
    rw [C.distance_eq x y,
      ENNReal.ofReal_rpow_of_nonneg hn hα,
      ← ENNReal.ofReal_mul (abs_nonneg A)]
    apply ENNReal.ofReal_le_ofReal
    exact (hh x y).trans (mul_le_mul_of_nonneg_right (le_abs_self A)
      (Real.rpow_nonneg (C.norm.gauge.2.1 _) _))
  exact (add_le_add hsup hsemi).trans_lt (ENNReal.add_lt_top.mpr
    ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

/-- A global compact intrinsic jet family with gauge-Hölder
bounds gives the exact fixed compact input on any open set containing
its zeroth support. Restriction uses the proved intrinsic transport API. -/
theorem memHolderXCompact_of_global_compact_gauge_jets {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X) (U : Opens (Fin N → ℝ))
    (k : ℕ) {α : ℝ} (hα : 0 ≤ α) {f : (Fin N → ℝ) → ℝ}
    (jet : List (Fin m) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ I, wordWeight w I ≤ k → hasIntrinsicWordDeriv X ⊤ I f (jet I))
    (hc : ∀ I, wordWeight w I ≤ k → Continuous (jet I))
    (hs : ∀ I, wordWeight w I ≤ k → HasCompactSupport (jet I))
    (hh : ∀ I, wordWeight w I ≤ k → ∃ A : ℝ, ∀ x y,
      |jet I x - jet I y| ≤ A * G2.gaugeDistance G C.norm x y ^ α)
    (hU : tsupport f ⊆ (U : Set (Fin N → ℝ))) :
    memHolderXCompact w X (controlDistance univ w X) U k α f := by
  have hnil : wordWeight w [] ≤ k := by simp [wordWeight]
  have hfI (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      holderENorm (controlDistance univ w X) α (U : Set (Fin N → ℝ)) (jet I) < ⊤ := by
    obtain ⟨A, hA⟩ := hh I hI
    exact (S.holderENorm_mono _ _ univ _ (subset_univ _)).trans_lt
      (holderENorm_finite_of_compact_gauge_holder G w X C hα (hc I hI) (hs I hI) hA)
  have hsf : HasCompactSupport f := hzero ▸ hs [] hnil
  have hcl : closure ((U : Set (Fin N → ℝ)) ∩ Function.support f) ⊆ tsupport f :=
    closure_mono inter_subset_right
  refine ⟨⟨hzero ▸ hfI [] hnil, ?_⟩,
    hsf.of_isClosed_subset isClosed_closure hcl, hcl.trans hU⟩
  intro I hI
  have hw := (S.mem_wordFamily_iff w k I).mp hI
  exact ⟨jet I, P2.hasIntrinsicWordDeriv_mono (subset_univ _) I (hi I hw), hfI I hw⟩

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicWeakHolderExport
public import RothschildStein.S.HolderWeakLocality
public import RothschildStein.S.ContinuousCompactZeroExtension
public import RothschildStein.S.ZeroExtension
public import RothschildStein.Definitions.memHolderXCompact
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.S.WeakIntrinsicWords
public import RothschildStein.S.WeakHolderRepresentatives
public import RothschildStein.S.Sobolev
public import RothschildStein.S.GroupControlGeometry
public import RothschildStein.H3.CompactGlobalHolderBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal
namespace RothschildStein.H3

/-- Under the global control-norm and metric-comparison hypotheses, a
compact intrinsic input supplies globally Hölder compact jets after zero
extension (BB Proposition 8.49, p. 379). -/
theorem exists_global_holder_intrinsic_jets_of_memHolderXCompact_of_controlNorm
    {N m : ℕ} (G : HomogeneousGroup N) (U : Opens (Fin N → ℝ))
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (C : G2.ControlNormConclusion G w X) (k : ℕ)
    {α : ℝ} (hα : 0 < α) {f : (Fin N → ℝ) → ℝ}
    (hf : memHolderXCompact w X (controlDistance univ w X) U k α f) :
    ∃ K : Compacts (Fin N → ℝ), (K : Set (Fin N → ℝ)) ⊆ U ∧
      ∃ jet : List (Fin m) → (Fin N → ℝ) → ℝ,
        jet [] = (U : Set (Fin N → ℝ)).indicator f ∧
        ∀ I, wordWeight w I ≤ k →
          hasIntrinsicWordDeriv X ⊤ I ((U : Set (Fin N → ℝ)).indicator f) (jet I) ∧
          Continuous (jet I) ∧ HasCompactSupport (jet I) ∧ tsupport (jet I) ⊆ K ∧
          ∃ A : ℝ, ∀ x y, |jet I x - jet I y| ≤ A * G2.gaugeDistance G C.norm x y ^ α := by
  classical
  let D := S.groupControlGeometry_of_controlNorm G w X C ⊤
  let K : Compacts (Fin N → ℝ) := ⟨closure ((U : Set (Fin N → ℝ)) ∩ Function.support f), hf.2.1⟩
  have hKU : (K : Set (Fin N → ℝ)) ⊆ U := hf.2.2
  have hz : ∀ x ∈ (U : Set (Fin N → ℝ)) \ K, f x = 0 := by
    intro x hx
    by_contra hn
    exact hx.2 (subset_closure ⟨hx.1, hn⟩)
  have hU : (U : Set (Fin N → ℝ)) ⊆ (⊤ : Opens (Fin N → ℝ)) := subset_univ _
  have hweak := S.memWeakHolderX_of_memHolderX ⊤ U D hU w X
    (fun i => (hX i).contDiffOn) k hα hf.1
  obtain ⟨v, hv0, hv⟩ := S.exists_weakHolder_representatives w X D.d U k α hweak
  let jet : List (Fin m) → (Fin N → ℝ) → ℝ := fun I => (U : Set (Fin N → ℝ)).indicator (v I)
  have hzero : jet [] = (U : Set (Fin N → ℝ)).indicator f := by
    change (U : Set (Fin N → ℝ)).indicator (v []) = _
    rw [hv0]
  have hcont (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      Continuous (jet I) ∧ HasCompactSupport (jet I) ∧ tsupport (jet I) ⊆ K := by
    have hi := hv I ((S.mem_wordFamily_iff w k I).mpr hI)
    have hc := S.continuousOn_of_holderENorm_lt_top_subset ⊤ D hU hα hi.2
    have hzv := S.weakHolder_derivative_zero_off_support ⊤ U D hU X I hα hi.1 hi.2 K.isCompact.isClosed hz
    exact S.continuous_compact_zeroExtension_of_local_support U hc K.isCompact hKU hzv
  have hw (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      hasWeakWordDeriv X ⊤ I ((U : Set (Fin N → ℝ)).indicator f) (jet I) := by
    exact S.hasWeakWordDeriv_zeroExtension X ⊤ U hU K hKU I f (v I)
      (hv I ((S.mem_wordFamily_iff w k I).mpr hI)).1
      (Eventually.of_forall fun x hu hk => hz x ⟨hu, hk⟩)
  have hh (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      ∃ A : ℝ, ∀ x y, |jet I x - jet I y| ≤ A * G2.gaugeDistance G C.norm x y ^ α := by
    let metric : MetricSpace (Fin N → ℝ) := S.groupControlMetric_of_controlNorm G w X C
    have hvI := hv I ((S.mem_wordFamily_iff w k I).mpr hI)
    have ht : holderSeminorm D.d α (U : Set (Fin N → ℝ)) (v I) < ⊤ :=
      (le_add_of_nonneg_left bot_le).trans_lt hvI.2
    have hb : ∀ x ∈ (U : Set (Fin N → ℝ)), ∀ y ∈ U,
        |jet I x - jet I y| ≤
          (holderSeminorm D.d α (U : Set (Fin N → ℝ)) (v I)).toReal *
            @dist (Fin N → ℝ) metric.toDist x y ^ α := by
      intro x hx y hy
      have hd : D.d x y < ⊤ := by
        change controlDistance univ w X x y < ⊤
        rw [C.distance_eq x y]
        exact ENNReal.ofReal_lt_top
      have he := S.holderSeminorm_increment_le D.d α (U : Set (Fin N → ℝ)) (v I) hα
        (fun a _ b _ hab => congrArg Subtype.val ((D.distance_eq_zero_iff ⟨a,mem_univ a⟩
          ⟨b,mem_univ b⟩).mp hab)) hx hy hd
      have hprod : holderSeminorm D.d α (U : Set (Fin N → ℝ)) (v I) * (D.d x y)^α ≠ ⊤ :=
        ENNReal.mul_ne_top ht.ne (ENNReal.rpow_ne_top_of_nonneg hα.le hd.ne)
      have hre := ENNReal.toReal_mono hprod he
      change |(U : Set (Fin N → ℝ)).indicator (v I) x -
        (U : Set (Fin N → ℝ)).indicator (v I) y| ≤ _
      rw [indicator_of_mem hx, indicator_of_mem hy]
      change |v I x - v I y| ≤
        (holderSeminorm D.d α (U : Set (Fin N → ℝ)) (v I)).toReal *
          G2.gaugeDistance G C.norm x y ^ α
      have hn : 0 ≤ G2.gaugeDistance G C.norm x y := C.norm.gauge.2.1 _
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
        ← ENNReal.toReal_rpow, D, S.groupControlGeometry_of_controlNorm, C.distance_eq,
        ENNReal.toReal_ofReal hn] using hre
    obtain ⟨A, _, hA⟩ := @exists_global_holder_bound_of_compact_support (Fin N → ℝ) metric
      (U : Set (Fin N → ℝ)) U.isOpen (jet I) (hcont I hI).1 (hcont I hI).2.1
      ((hcont I hI).2.2.trans hKU) α
      (holderSeminorm D.d α (U : Set (Fin N → ℝ)) (v I)).toReal hα hb
    exact ⟨A, hA⟩
  refine ⟨K, hKU, jet, hzero, ?_⟩
  intro I hI
  refine ⟨?_, (hcont I hI).1, (hcont I hI).2.1, (hcont I hI).2.2, hh I hI⟩
  exact S.hasIntrinsicWordDeriv_of_continuous_weak_subwords ⊤ X
    (fun i => (hX i).contDiffOn) I ((U : Set (Fin N → ℝ)).indicator f) jet hzero
    (fun J hJ => hw J ((S.wordWeight_sublist_le w hJ).trans hI))
    (fun J hJ => (hcont J ((S.wordWeight_sublist_le w hJ).trans hI)).1.continuousOn)

end RothschildStein.H3

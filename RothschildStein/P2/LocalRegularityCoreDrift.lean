-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityCharts

/-!
# Local regularity assembly: the drift roots in a system with `n ≥ 3`

`rs3_drift_sobolev_core` and `rs3_drift_holder_core` are the statements of
`rs3_drift_sobolev` and `rs3_drift_holder` (BB Thm 11.2, `k = 0`) for a system of dimension `n ≥ 3`
(extra hypothesis `3 ≤ n`, used for the model hypothesis `Q ≥ 3` of the chain), assuming the
upstream bundles. This is the chain of the drift regularity theorem:

* the distributional smoothing theorem gives the order-two representative `u` (`smoothing_sobolev_of_localSolvability`,
  `smoothing_holder_of_localSolvability`), lifted charts coming from the lifting theorem statement and
  the rank condition (`hchart_drift`);
* strong solutions: `u` solves `L u = f` strongly (`LocalRegularityStrong`);
* the base Sobolev estimate / the base Hölder estimate with the finite cover: the estimate on `V ⋐ W` (`sobolev_transfer_cover_drift_of_lifted`,
  `holder_finite_cover_drift_of_lifted`).

The padded theorems `rs3_*_of_hypotheses` (`LocalRegularityRoot*`) reduce arbitrary `n ≥ 1` to this case.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

/-- The statement of `rs3_drift_sobolev` for systems with `3 ≤ n`,
assuming the lifting theorem, left differentiation `LeftDifferentiation` (which gives local solvability) and the base Sobolev estimate. -/
theorem rs3_drift_sobolev_core (U : DriftSobolevHypotheses)
    {n q : ℕ} (hn3 : 3 ≤ n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memSobolevX driftWeight X Ω 0 p f →
        hasDistributionEquationWithDrift Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          memSobolevXLoc driftWeight X Ω 2 p u ∧
          sobolevXENorm driftWeight X V 2 p u ≤
            ENNReal.ofReal C *
              (sobolevXENorm driftWeight X W 0 p f +
                eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) := by
  have hn : 0 < n := by omega
  have hWΩ' : (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hWΩ
  have hWle : W ≤ Ω := hWΩ'
  have hVΩ : closure (V : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := hVW.trans hWΩ'
  have hchart := hchart_drift U.liftApproximation hn hq Ω X hX hspan
  have hSolv : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m),
      LocalSolvability C := fun _ _ _ C => localSolvabilityAllChartsDrift_of_leftDifferentiation U.leftDifferentiation hn3 hq C
  obtain ⟨st, hst⟩ := exists_uniform_liftedCharts_drift U.liftApproximation hn hq Ω X hX hspan hV hVΩ
  have hcharts : ∀ x ∈ closure (V : Set (Fin n → ℝ)), ∃ m : ℕ,
      ∃ C : P1.LiftedChart driftWeight st (Ω : Set (Fin n → ℝ)) Ω.isOpen X x m,
        ∃ ν : G2.HomogeneousNorm C.G,
          LiftedBaseSobolevEstimate C ν (driftOpWords q) p := by
    intro x hx
    obtain ⟨m, ⟨C⟩⟩ := hst x hx
    exact ⟨m, C, G2.smoothNorm C.G, U.lifted hn3 hq C hp hp_top⟩
  obtain ⟨Cst, hCst, hbound⟩ := sobolev_transfer_cover_drift_of_lifted hp.le hp_top.ne V W hV hVW
    hWΩ' hcharts
  refine ⟨Cst, hCst, fun T f hf hT => ?_⟩
  obtain ⟨u, huloc, hTu, hu2⟩ := smoothing_sobolev_of_localSolvability Ω X hX hchart hSolv hp hp_top
    T f hf hT
  refine ⟨u, huloc, hTu, hu2, ?_⟩
  have huW : memSobolevX driftWeight X W 2 p u := hu2 W hW hWΩ
  have hTW : hasDistributionEquationWithDrift W X (fun i => (hX i).mono hWΩ')
      (Distribution.ofFun W u volume (⊤ : ℕ∞)) f := by
    have h1 := hasDistributionEquationWithDrift_restrict Ω W hWle X hX hT
    rwa [hTu, distributionRestrictionCLM_ofFun Ω W hWle huloc] at h1
  have hop := hasWeakOperatorValue_drift_of_equation W X (fun i => (hX i).mono hWΩ') hTW huW
  rw [sobolevXENorm_zero_eq_eLpNorm driftWeight X W hp.le f]
  exact hbound u f huW hop

/-- The statement of `rs3_drift_holder` for systems with `3 ≤ n`,
assuming the lifting theorem, left differentiation `LeftDifferentiation` (which gives local solvability), the local doubling property and the base Hölder estimate. -/
theorem rs3_drift_holder_core (U : DriftHolderHypotheses)
    {n q : ℕ} (hn3 : 3 ≤ n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let d := controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memHolderX driftWeight X d Ω 0 α f →
        hasDistributionEquationWithDrift Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          ContinuousOn u (Ω : Set (Fin n → ℝ)) ∧
          memHolderXLoc driftWeight X d Ω 2 α u ∧
          holderXENorm driftWeight X d V 2 α u ≤
            ENNReal.ofReal C *
              (holderXENorm driftWeight X d W 0 α f +
                eLpNorm u ⊤ (volume.restrict (W : Set (Fin n → ℝ)))) ∧
          ∃ g : Fin (q + 1) → (Fin n → ℝ) → ℝ,
            hasIntrinsicWordDeriv X Ω [0] u (g 0) ∧
            (∀ i : Fin q,
              hasIntrinsicWordDeriv X Ω [i.succ, i.succ] u (g i.succ)) ∧
            (∀ x ∈ (Ω : Set (Fin n → ℝ)),
              (∑ i : Fin q, g i.succ x) + g 0 x = f x) := by
  intro d
  have hn : 0 < n := by omega
  have hWΩ' : (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hWΩ
  have hVΩ : closure (V : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := hVW.trans hWΩ'
  have hchart := hchart_drift U.liftApproximation hn hq Ω X hX hspan
  have hSolv : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m),
      LocalSolvability C := fun _ _ _ C => localSolvabilityAllChartsDrift_of_leftDifferentiation U.leftDifferentiation hn3 hq C
  have hdbl : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m),
      OriginalLocalDoubling (Ω : Set (Fin n → ℝ)) driftWeight X (basePoint '' C.U) :=
    fun _ _ _ C => U.doubling hn3 hq hX hspan C
  obtain ⟨st, hst⟩ := exists_uniform_liftedCharts_drift U.liftApproximation hn hq Ω X hX hspan hV hVΩ
  have hcharts : ∀ x ∈ closure (V : Set (Fin n → ℝ)), ∃ m : ℕ,
      ∃ C : P1.LiftedChart driftWeight st (Ω : Set (Fin n → ℝ)) Ω.isOpen X x m,
        ∃ ν : G2.HomogeneousNorm C.G,
          LiftedBaseHolderEstimate C ν (driftOpWords q) α := by
    intro x hx
    obtain ⟨m, ⟨C⟩⟩ := hst x hx
    exact ⟨m, C, G2.smoothNorm C.G, U.lifted hn3 hq C hα hα1⟩
  obtain ⟨Cst, hCst, hbound⟩ := holder_finite_cover_drift_of_lifted hα hα1 V W hV hVW hWΩ'
    (fun x _ m C => U.doubling hn3 hq hX hspan C) hcharts
  refine ⟨Cst, hCst, fun T f hf hT => ?_⟩
  obtain ⟨u, huloc, hTu, huc, hglob, hnear⟩ := smoothing_holder_of_localSolvability Ω X hX hchart
    hSolv hdbl hα hα1 T f hf hT
  -- the local form `memHolderXLoc` (finite cover, as in `holderENorm_lt_top_of_local_balls`)
  have hloc : memHolderXLoc driftWeight X d Ω 2 α u := by
    intro V' hVc hVΩ'
    have hV'Ω' : (V' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hVΩ'
    refine ⟨holderENorm_lt_top_of_local_balls Ω X hX hchart hα hα1.le hVc hVΩ'
      (fun y hy => ?_), fun I hI => ?_⟩
    · obtain ⟨A, hyA, hAΩ, hmem⟩ := hnear y hy
      exact ⟨A, hyA, hAΩ, hmem.1⟩
    · obtain ⟨g, -, -, hgI⟩ := hglob I hI
      refine ⟨g, hasIntrinsicWordDeriv_mono hV'Ω' I hgI,
        holderENorm_lt_top_of_local_balls Ω X hX hchart hα hα1.le hVc hVΩ' (fun y hy => ?_)⟩
      obtain ⟨A, hyA, hAΩ, hmem⟩ := hnear y hy
      obtain ⟨g', hg', hfin'⟩ := hmem.2 I hI
      have hgA := hasIntrinsicWordDeriv_mono (V := Ω) (V' := A) hAΩ I hgI
      have huniq := RothschildStein.S.hasIntrinsicWordDeriv_unique A X I hg' hgA
      refine ⟨A, hyA, hAΩ, ?_⟩
      rw [holderENorm_congr (fun x hx => (huniq hx).symm)]
      exact hfin'
  -- the strong (intrinsic) equation
  have hfc : ContinuousOn f (Ω : Set (Fin n → ℝ)) :=
    continuousOn_of_holderENorm_charts hchart hα hf.1
  choose g hgc hgw hgi using fun i : Fin (q + 1) =>
    hglob (driftOpWords q i) (driftOpWords_mem_wordFamily q i)
  have hT' : hasDistributionEquationWithDrift Ω X hX (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f := by
    rwa [hTu] at hT
  have heq := eqOn_sum_weakDerivs_drift Ω X hX hT' hfc hgc hgw
  have hopW : HasIntrinsicOperatorValue X W (driftOpWords q) u f :=
    ⟨g, fun i => hasIntrinsicWordDeriv_mono hWΩ' _ (hgi i), fun x hx => heq x (hWΩ' hx)⟩
  refine ⟨u, huloc, hTu, huc, hloc, hbound u f (hloc W hW hWΩ) hopW, g, ?_, ?_, ?_⟩
  · simpa [driftOpWords] using hgi 0
  · intro i
    simpa [driftOpWords, Fin.succ_ne_zero] using hgi i.succ
  · intro x hx
    have h := heq x hx
    rw [Fin.sum_univ_succ] at h
    linarith

end RothschildStein.P2

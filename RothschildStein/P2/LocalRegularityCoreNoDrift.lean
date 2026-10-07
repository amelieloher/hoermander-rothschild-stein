-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityCharts

/-!
# Local regularity assembly: the no-drift roots in a system with `n ≥ 3`

`rs3_no_drift_sobolev_core` and `rs3_no_drift_holder_core` are the statements of
`rs3_no_drift_sobolev` and `rs3_no_drift_holder` (BB Thm 11.1, all `k`) for a system of dimension
`n ≥ 3` (extra hypothesis `3 ≤ n`), assuming the upstream bundles. This is the chain of
the regularity theorem without drift:

* the distributional smoothing theorem gives the order-two representative `u` (`smoothing_sobolev_noDrift_of_localSolvability`,
  `smoothing_holder_noDrift_of_localSolvability`), lifted charts coming from the lifting theorem
  statement and the rank condition (`hchart_noDrift`);
* strong solutions: `u` solves `L u = f` strongly (`LocalRegularityStrong`);
* the higher Sobolev estimate / the higher Hölder estimate on nested compact domains (`HigherSobolevRegularityNoDrift`, `HigherHolderRegularityNoDrift`): the
  order-`k + 2` regularity on every `V' ⋐ Ω` and the estimate on `V ⋐ W`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

/-- An open set strictly between a compact-closure open set and the domain: for `V' ⋐ Ω` there is
`W'` open with `closure V' ⊆ W'`, `closure W'` compact and contained in `Ω`. -/
theorem exists_open_between_closure {n : ℕ} (Ω V' : Opens (Fin n → ℝ))
    (hVc : IsCompact (closure (V' : Set (Fin n → ℝ))))
    (hVΩ : closure (V' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ))) :
    ∃ W' : Opens (Fin n → ℝ), closure (V' : Set (Fin n → ℝ)) ⊆ (W' : Set (Fin n → ℝ)) ∧
      IsCompact (closure (W' : Set (Fin n → ℝ))) ∧
      closure (W' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := by
  obtain ⟨W', hW'o, hVW', hW'Ω, hW'c⟩ :=
    exists_open_between_and_isCompact_closure hVc Ω.isOpen hVΩ
  exact ⟨⟨W', hW'o⟩, hVW', hW'c, hW'Ω⟩

/-- The statement of `rs3_no_drift_sobolev` for systems with `3 ≤ n`,
assuming the lifting theorem, left differentiation `LeftDifferentiation` (which gives local solvability) and the higher Sobolev estimate. -/
theorem rs3_no_drift_sobolev_core (U : NoDriftSobolevHypotheses)
    {n q : ℕ} (hn3 : 3 ≤ n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (k : ℕ)
    (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memSobolevX noDriftWeight X Ω k p f →
        hasDistributionEquation Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          memSobolevXLoc noDriftWeight X Ω (k + 2) p u ∧
          sobolevXENorm noDriftWeight X V (k + 2) p u ≤
            ENNReal.ofReal C *
              (sobolevXENorm noDriftWeight X W k p f +
                eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) := by
  have hn : 0 < n := by omega
  have hWΩ' : (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hWΩ
  have hchart := hchart_noDrift U.liftApproximation hn hq Ω X hX hspan
  have hSolv : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart noDriftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m),
      LocalSolvabilityNoDrift C := fun _ _ _ C => localSolvabilityAllChartsNoDrift_of_leftDifferentiation U.leftDifferentiation hn3 hq C
  obtain ⟨C, hC, hhigh⟩ := U.higher hn3 Ω V W X hX hspan hV hVW hW hWΩ k p hp hp_top
  refine ⟨C, hC, fun T f hf hT => ?_⟩
  obtain ⟨u, huloc, hTu, hu2⟩ := smoothing_sobolev_noDrift_of_localSolvability Ω X hX hchart
    hSolv hp hp_top T f (RothschildStein.S.memSobolevX_mono_order noDriftWeight X Ω (Nat.zero_le k) hf)
    hT
  have hT' : hasDistributionEquation Ω X hX (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f := by
    rwa [hTu] at hT
  -- the strong solution on every `W' ⋐ Ω`
  have hstrong : ∀ W' : Opens (Fin n → ℝ), IsCompact (closure (W' : Set (Fin n → ℝ))) →
      closure (W' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) →
      memSobolevX noDriftWeight X W' 2 p u ∧
        HasWeakOperatorValue X W' (noDriftOpWords q) u f := by
    intro W' hW'c hW'Ω
    have hW'Ω' : (W' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hW'Ω
    have hW'le : W' ≤ Ω := hW'Ω'
    have huW' : memSobolevX noDriftWeight X W' 2 p u := hu2 W' hW'c hW'Ω
    have hTW' : hasDistributionEquation W' X (fun i => (hX i).mono hW'Ω')
        (Distribution.ofFun W' u volume (⊤ : ℕ∞)) f := by
      have h1 := hasDistributionEquation_restrict_noDrift Ω W' hW'le X hX hT'
      rwa [distributionRestrictionCLM_ofFun Ω W' hW'le huloc] at h1
    exact ⟨huW', hasWeakOperatorValue_noDrift_of_equation W' X (fun i => (hX i).mono hW'Ω') hTW'
      huW'⟩
  refine ⟨u, huloc, hTu, fun V' hV'c hV'Ω => ?_, ?_⟩
  · -- order `k + 2` on `V' ⋐ Ω` through an intermediate `W'`
    obtain ⟨W', hVW', hW'c, hW'Ω⟩ := exists_open_between_closure Ω V' hV'c hV'Ω
    obtain ⟨C', -, hhigh'⟩ := U.higher hn3 Ω V' W' X hX hspan hV'c hVW' hW'c hW'Ω k p hp hp_top
    obtain ⟨huW', hopW'⟩ := hstrong W' hW'c hW'Ω
    have hfW' : memSobolevX noDriftWeight X W' k p f :=
      RothschildStein.S.memSobolevX_restrict noDriftWeight X Ω W' (subset_closure.trans hW'Ω) hf
    exact (hhigh' u f huW' hopW' hfW').1
  · obtain ⟨huW, hopW⟩ := hstrong W hW hWΩ
    have hfW : memSobolevX noDriftWeight X W k p f :=
      RothschildStein.S.memSobolevX_restrict noDriftWeight X Ω W hWΩ' hf
    exact (hhigh u f huW hopW hfW).2

/-- The statement of `rs3_no_drift_holder` for systems with `3 ≤ n`,
assuming the lifting theorem, left differentiation `LeftDifferentiation` (which gives local solvability), the local doubling property and the higher Hölder estimate. -/
theorem rs3_no_drift_holder_core (U : NoDriftHolderHypotheses)
    {n q : ℕ} (hn3 : 3 ≤ n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (k : ℕ)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let d := controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memHolderX noDriftWeight X d Ω k α f →
        hasDistributionEquation Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          ContinuousOn u (Ω : Set (Fin n → ℝ)) ∧
          memHolderXLoc noDriftWeight X d Ω (k + 2) α u ∧
          holderXENorm noDriftWeight X d V (k + 2) α u ≤
            ENNReal.ofReal C *
              (holderXENorm noDriftWeight X d W k α f +
                eLpNorm u ⊤ (volume.restrict (W : Set (Fin n → ℝ)))) ∧
          ∃ g : Fin q → (Fin n → ℝ) → ℝ,
            (∀ i, hasIntrinsicWordDeriv X Ω [i, i] u (g i)) ∧
            (∀ x ∈ (Ω : Set (Fin n → ℝ)), (∑ i, g i x) = f x) := by
  intro d
  have hn : 0 < n := by omega
  have hWΩ' : (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hWΩ
  have hchart := hchart_noDrift U.liftApproximation hn hq Ω X hX hspan
  have hSolv : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart noDriftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m),
      LocalSolvabilityNoDrift C := fun _ _ _ C => localSolvabilityAllChartsNoDrift_of_leftDifferentiation U.leftDifferentiation hn3 hq C
  have hdbl : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart noDriftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m),
      OriginalLocalDoubling (Ω : Set (Fin n → ℝ)) noDriftWeight X (basePoint '' C.U) :=
    fun _ _ _ C => U.doubling hn3 hX hspan C
  obtain ⟨C, hC, hhigh⟩ := U.higher hn3 Ω V W X hX hspan hV hVW hW hWΩ k α hα hα1
  refine ⟨C, hC, fun T f hf hT => ?_⟩
  have hf0 : memHolderX noDriftWeight X d Ω 0 α f :=
    (RothschildStein.S.memHolderX_zero_iff noDriftWeight X d Ω α f).2 hf.1
  obtain ⟨u, huloc, hTu, huc, hglob, hnear⟩ := smoothing_holder_noDrift_of_localSolvability Ω X
    hX hchart hSolv hdbl hα hα1 T f hf0 hT
  -- the local form `memHolderXLoc` of order 2 (finite cover)
  have hloc : memHolderXLoc noDriftWeight X d Ω 2 α u := by
    intro V' hVc hVΩ'
    have hV'Ω' : (V' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hVΩ'
    refine ⟨holderENorm_lt_top_of_local_balls_noDrift Ω X hX hchart hα hα1.le hVc hVΩ'
      (fun y hy => ?_), fun I hI => ?_⟩
    · obtain ⟨A, hyA, hAΩ, hmem⟩ := hnear y hy
      exact ⟨A, hyA, hAΩ, hmem.1⟩
    · obtain ⟨g, -, -, hgI⟩ := hglob I hI
      refine ⟨g, hasIntrinsicWordDeriv_mono hV'Ω' I hgI,
        holderENorm_lt_top_of_local_balls_noDrift Ω X hX hchart hα hα1.le hVc hVΩ'
          (fun y hy => ?_)⟩
      obtain ⟨A, hyA, hAΩ, hmem⟩ := hnear y hy
      obtain ⟨g', hg', hfin'⟩ := hmem.2 I hI
      have hgA := hasIntrinsicWordDeriv_mono (V := Ω) (V' := A) hAΩ I hgI
      have huniq := RothschildStein.S.hasIntrinsicWordDeriv_unique A X I hg' hgA
      refine ⟨A, hyA, hAΩ, ?_⟩
      rw [holderENorm_congr (fun x hx => (huniq hx).symm)]
      exact hfin'
  -- the strong (intrinsic) equation on `Ω`
  have hfc : ContinuousOn f (Ω : Set (Fin n → ℝ)) :=
    continuousOn_of_holderENorm_charts hchart hα hf.1
  choose g hgc hgw hgi using fun i : Fin q =>
    hglob (noDriftOpWords q i) (noDriftOpWords_mem_wordFamily q i)
  have hT' : hasDistributionEquation Ω X hX (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f := by
    rwa [hTu] at hT
  have heq := eqOn_sum_weakDerivs_noDrift Ω X hX hT' hfc hgc hgw
  have hstrong : ∀ W' : Opens (Fin n → ℝ), closure (W' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) →
      IsCompact (closure (W' : Set (Fin n → ℝ))) →
      memHolderX noDriftWeight X d W' 2 α u ∧
        HasIntrinsicOperatorValue X W' (noDriftOpWords q) u f ∧
        memHolderX noDriftWeight X d W' k α f := by
    intro W' hW'Ω hW'c
    have hW'Ω' : (W' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hW'Ω
    exact ⟨hloc W' hW'c hW'Ω,
      ⟨g, fun i => hasIntrinsicWordDeriv_mono hW'Ω' _ (hgi i), fun x hx => heq x (hW'Ω' hx)⟩,
      memHolderX_mono_domain noDriftWeight hW'Ω' hf⟩
  refine ⟨u, huloc, hTu, huc, fun V' hV'c hV'Ω => ?_, ?_, g, fun i => ?_, fun x hx => heq x hx⟩
  · -- order `k + 2` on `V' ⋐ Ω` through an intermediate `W'`
    obtain ⟨W', hVW', hW'c, hW'Ω⟩ := exists_open_between_closure Ω V' hV'c hV'Ω
    obtain ⟨C', -, hhigh'⟩ := U.higher hn3 Ω V' W' X hX hspan hV'c hVW' hW'c hW'Ω k α hα hα1
    obtain ⟨huW', hopW', hfW'⟩ := hstrong W' hW'Ω hW'c
    exact (hhigh' u f huW' hopW' hfW').1
  · obtain ⟨huW, hopW, hfW⟩ := hstrong W hWΩ hW
    exact (hhigh u f huW hopW hfW).2
  · simpa [noDriftOpWords] using hgi i

end RothschildStein.P2

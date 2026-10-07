-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingGlue

/-!
# Distributional smoothing (BB Thm 11.62, (11.101), pp. 608-610)

With drift allowed, `T ∈ 𝒟'(Ω)`, `L T = f`, `L = ∑ Xᵢ² + X₀`:

* `f ∈ L^p(Ω)`, `1 < p < ∞` implies a representative `u ∈ W^{2,p}_{X,loc}(Ω)`
  (`smoothing_sobolev_of_localSolvability`, `memSobolevXLoc`);
* `f ∈ C^α_X(Ω)`, `0 < α < 1` implies a continuous representative `u` of `T` all of whose words
  of weight at most two are continuous (intrinsic) derivatives on `Ω`, and `u ∈ C^{2,α}_X(A)` on a
  base control ball `A` around every point (`smoothing_holder_of_localSolvability`, `memHolderX`);
  `holderENorm_lt_top_of_local_balls` (`SmoothingTheoremCover`) upgrades this to `memHolderXLoc` (every `V ⋐ Ω`) by the finite-cover argument.

Proof (BB pp. 608-610): lift `T̃ = T ∘ J` in a lifted chart (`SmoothingChart`),
`L̃ T̃ = f̃` (adjoint intertwining); local solvability (`LocalSolvability`) gives a particular solution `v`; `T̃ - v`
is smooth (the homogeneous hypoellipticity statement); so `T̃ = v + H` is in `W^{2,p}` / `C^{2,α}` on relatively compact balls
(`solve_subtract_*`, `SmoothingSolve`); descend on a cylinder (`SmoothingDescent`) and glue the
local representatives (`SmoothingGlue`); in the Hölder case the Hölder norm of the glued
representative on a base control ball is controlled by that of its lift on a lifted control ball
(Hölder transfer, `holderTransfer_of_doubling`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section LocalToGlobal

variable {N k₀ : ℕ}

/-- `L^p` membership on a compact set from `L^p` membership on a neighborhood of each of its points
(a finite subcover of the closure; `1 ≤ p < ∞`). -/
theorem memLp_of_local_cover {Ω V : Opens (Fin N → ℝ)}
    (hVc : IsCompact (closure (V : Set (Fin N → ℝ)))) (hVΩ : closure (V : Set (Fin N → ℝ)) ⊆ Ω)
    {G : (Fin N → ℝ) → ℝ} (hG : LocallyIntegrableOn G (Ω : Set (Fin N → ℝ)) volume) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hloc : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ A : Opens (Fin N → ℝ), x ∈ (A : Set (Fin N → ℝ)) ∧
      A ≤ Ω ∧ MemLp G p (volume.restrict (A : Set (Fin N → ℝ)))) :
    MemLp G p (volume.restrict (V : Set (Fin N → ℝ))) := by
  choose! A hxA hAΩ hAL using hloc
  obtain ⟨t, ht⟩ := hVc.elim_nhds_subcover' (fun x _ => (A x : Set (Fin N → ℝ)))
    (fun x hx => (A x).isOpen.mem_nhds (hxA x (hVΩ hx)))
  have hint : IntegrableOn (fun x => ‖G x‖ ^ p.toReal)
      (⋃ x ∈ t, (A x : Set (Fin N → ℝ))) volume := by
    refine integrableOn_finset_iUnion.2 fun x _ => ?_
    exact (hAL x (hVΩ x.2)).integrable_norm_rpow hp0 hpt
  have hmeas : AEStronglyMeasurable G (volume.restrict (V : Set (Fin N → ℝ))) :=
    ((hG.integrableOn_compact_subset hVΩ hVc).aestronglyMeasurable).mono_set subset_closure
  refine (integrable_norm_rpow_iff hmeas hp0 hpt).1 ?_
  exact hint.mono_set (subset_closure.trans ht)

/-- A locally integrable function on `Ω`, all of whose weak word derivatives exist and are `L^p` on a
neighborhood of each point, is in the weighted Sobolev class on every `V ⋐ Ω` (finite cover and
gluing of weak derivatives; `1 ≤ p < ∞`). -/
theorem memSobolevXLoc_of_local (wt : Fin k₀ → ℕ+) (Xa : Fin k₀ → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xa i) (Ω : Set (Fin N → ℝ)))
    {kk : ℕ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {F : (Fin N → ℝ) → ℝ}
    (hF : LocallyIntegrableOn F (Ω : Set (Fin N → ℝ)) volume)
    (hloc : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ A : Opens (Fin N → ℝ), x ∈ (A : Set (Fin N → ℝ)) ∧
      A ≤ Ω ∧ memSobolevX wt Xa A kk p F) :
    memSobolevXLoc wt Xa Ω kk p F := by
  intro V hVc hVΩ
  have hVΩ' : (V : Set (Fin N → ℝ)) ⊆ Ω := subset_closure.trans hVΩ
  choose A hxA hAΩ hmem using fun x : Ω => hloc x x.2
  have hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i : Ω, x ∈ (A i : Set (Fin N → ℝ)) :=
    fun x hx => ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩
  refine ⟨memLp_of_local_cover hVc hVΩ hF hp0 hpt (fun x hx => ?_), fun I hI => ?_⟩
  · exact ⟨A ⟨x, hx⟩, hxA ⟨x, hx⟩, hAΩ ⟨x, hx⟩, (hmem ⟨x, hx⟩).1⟩
  · choose g hg hgL using fun x : Ω => (hmem x).2 I hI
    obtain ⟨G, hG, hGae⟩ := exists_hasWeakWordDeriv_gluing Xa Ω hX I hF A hAΩ hcover g hg
    refine ⟨G, RothschildStein.S.hasWeakWordDeriv_restrict Xa Ω V hVΩ' hG,
      memLp_of_local_cover hVc hVΩ hG.2.1 hp0 hpt (fun x hx => ?_)⟩
    exact ⟨A ⟨x, hx⟩, hxA ⟨x, hx⟩, hAΩ ⟨x, hx⟩, (hgL ⟨x, hx⟩).ae_eq (hGae ⟨x, hx⟩).symm⟩

/-- Sobolev membership is invariant under a.e. changes of the function. -/
theorem memSobolevX_congr_ae (wt : Fin k₀ → ℕ+) (Xa : Fin k₀ → (Fin N → ℝ) → (Fin N → ℝ))
    (V : Opens (Fin N → ℝ)) {kk : ℕ} {p : ℝ≥0∞} {f f' : (Fin N → ℝ) → ℝ}
    (h : memSobolevX wt Xa V kk p f) (hae : f =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f') :
    memSobolevX wt Xa V kk p f' := by
  refine ⟨h.1.ae_eq hae, fun I hI => ?_⟩
  obtain ⟨g, hg, hgL⟩ := h.2 I hI
  exact ⟨g, RothschildStein.S.hasWeakWordDeriv_congr_ae Xa V hg hae Filter.EventuallyEq.rfl, hgL⟩

end LocalToGlobal

section Sobolev

variable {n q : ℕ}

/-- **Distributional smoothing, `L^p` case (BB Thm 11.62, pp. 608-610), under a `LocalSolvability` hypothesis.** Let `Ω ⊆ ℝⁿ` be open, `X = (X₀, …, X_q)` smooth fields on `Ω` (`X₀` the drift, weight 2),
`T ∈ 𝒟'(Ω)` with `L T = f` (`hasDistributionEquationWithDrift`), `f ∈ L^p(Ω)`,
`1 < p < ∞`. Then `T` has a representative `u ∈ L¹_loc(Ω)` with `u ∈ W^{2,p}_{X,loc}(Ω)` (`memSobolevXLoc`).

The hypotheses are the inputs to the proof: `hchart` is the conclusion of the
lifting theorem `exists_lift_approximation_drift` at every point (a lifted chart, as supplied by
`liftedChart_of_drift`; the Hörmander condition enters through it) and `hSolv` is the statement
local solvability (`LocalSolvability`) for every lifted chart. -/
theorem smoothing_sobolev_of_localSolvability (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hchart : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m))
    (hSolv : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m), LocalSolvability C)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p < ⊤) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (f : (Fin n → ℝ) → ℝ) (hf : memSobolevX driftWeight X Ω 0 p f)
    (hT : hasDistributionEquationWithDrift Ω X hX T f) :
    ∃ u : (Fin n → ℝ) → ℝ, LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
      T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧ memSobolevXLoc driftWeight X Ω 2 p u := by
  -- local representatives near every point
  have hlocal : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ A : Opens (Fin n → ℝ),
      x₀ ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ Ω ∧ ∃ u : (Fin n → ℝ) → ℝ,
        representsDistribution A (RothschildStein.S.distributionRestrictionCLM Ω A T) u ∧
          memSobolevX driftWeight X A 2 p u := by
    intro x₀ hx₀
    obtain ⟨s, m, ⟨C⟩⟩ := hchart x₀ hx₀
    exact exists_local_representative_sobolev_of_localSolvability C (hSolv x₀ s m C) hp hp_top T hf.1 hT
  choose! A hxA hAΩ u hrep hmem using hlocal
  obtain ⟨F, hFloc, hTF, hFae⟩ := exists_locallyIntegrable_gluing Ω T (fun x : Ω => A x)
    (fun x => u x) (fun x => hAΩ x x.2) (fun x hx => ⟨⟨x, hx⟩, hxA x hx⟩)
    (fun x => (hrep x x.2).1)
    (fun x ψ hψ => integral_eq_of_representsDistribution Ω (A x) (hAΩ x x.2) T (hrep x x.2) ψ hψ)
  refine ⟨F, hFloc, hTF, memSobolevXLoc_of_local driftWeight X Ω hX
    (zero_lt_one.trans hp).ne' hp_top.ne hFloc (fun x hx => ?_)⟩
  exact ⟨A x, hxA x hx, hAΩ x hx, memSobolevX_congr_ae driftWeight X (A x) (hmem x hx)
    (hFae ⟨x, hx⟩).symm⟩

end Sobolev

section HolderTools

variable {N k₀ : ℕ}

/-- The intrinsic word derivative depends on the function only through its values on `V`. -/
theorem hasIntrinsicWordDeriv_congr_left {Xa : Fin k₀ → (Fin N → ℝ) → (Fin N → ℝ)}
    {V : Opens (Fin N → ℝ)} {f f' : (Fin N → ℝ) → ℝ} (h : EqOn f' f (V : Set (Fin N → ℝ))) :
    ∀ (I : List (Fin k₀)) {g : (Fin N → ℝ) → ℝ}, hasIntrinsicWordDeriv Xa V I f g →
      hasIntrinsicWordDeriv Xa V I f' g
  | [], _, hg => fun _ hx => (hg hx).trans (h hx).symm
  | _ :: I, _, ⟨a, ha, hga⟩ => ⟨a, hasIntrinsicWordDeriv_congr_left h I ha, hga⟩

/-- A function equal on `V` to a member of `C^{k,α}_X(V)` has finite weighted Hölder norm. -/
theorem holderXENorm_lt_top_of_memHolderX_congr (wt : Fin k₀ → ℕ+)
    (Xa : Fin k₀ → (Fin N → ℝ) → (Fin N → ℝ)) (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (V : Opens (Fin N → ℝ)) {kk : ℕ} {α : ℝ} {f f' : (Fin N → ℝ) → ℝ}
    (hmem : memHolderX wt Xa d V kk α f) (heq : EqOn f' f (V : Set (Fin N → ℝ))) :
    holderXENorm wt Xa d V kk α f' < ⊤ := by
  unfold holderXENorm
  refine ENNReal.sum_lt_top.2 fun I hI => ?_
  obtain ⟨g, hg, hgn⟩ := hmem.2 I hI
  exact lt_of_le_of_lt (sInf_le ⟨g, hasIntrinsicWordDeriv_congr_left heq I hg, rfl⟩) hgn

/-- Finite weighted Hölder norm is membership in `C^{k,α}_X(V)`: for each word the infimum is
attained below `⊤`, by a function with finite Hölder norm. -/
theorem memHolderX_of_holderXENorm_lt_top (wt : Fin k₀ → ℕ+)
    (Xa : Fin k₀ → (Fin N → ℝ) → (Fin N → ℝ)) (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (V : Opens (Fin N → ℝ)) {kk : ℕ} {α : ℝ} {f : (Fin N → ℝ) → ℝ}
    (h : holderXENorm wt Xa d V kk α f < ⊤) : memHolderX wt Xa d V kk α f := by
  have hI : ∀ I ∈ wordFamily wt kk, ∃ g : (Fin N → ℝ) → ℝ, hasIntrinsicWordDeriv Xa V I f g ∧
      holderENorm d α (V : Set (Fin N → ℝ)) g < ⊤ := by
    intro I hI
    have h1 : intrinsicWordENorm Xa d V I α f < ⊤ := lt_of_le_of_lt
      (Finset.single_le_sum (f := fun J => intrinsicWordENorm Xa d V J α f)
        (fun _ _ => zero_le) hI) h
    obtain ⟨r, ⟨g, hg, rfl⟩, hr⟩ := sInf_lt_iff.1 h1
    exact ⟨g, hg, hr⟩
  refine ⟨?_, hI⟩
  obtain ⟨g, hg, hgn⟩ := hI [] (RothschildStein.S.nil_mem_wordFamily wt kk)
  rw [holderENorm_congr (fun x hx => (hg hx).symm : EqOn f g (V : Set (Fin N → ℝ)))]
  exact hgn

end HolderTools

section Hölder

variable {n q : ℕ}

/-- Base control balls are Euclidean open, given a lifted chart at every point of `Ω` (Euclidean
convergence implies convergence of the control distance at each point, through the lift). -/
theorem isOpen_rsBall_base (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hchart : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m))
    (x : Fin n → ℝ) (r : ℝ) :
    IsOpen (rsBall (Ω : Set (Fin n → ℝ)) driftWeight X x r) := by
  refine isOpen_rsBall_of_close (N := (Ω : Set (Fin n → ℝ))) subset_rfl (fun y hy ε hε => ?_)
    (fun z hz => hz.1)
  obtain ⟨s, m, ⟨C⟩⟩ := hchart y hy
  have hmem : y ∈ basePoint '' C.U :=
    ⟨joinPoint y (0 : Fin m → ℝ), C.center_mem, basePoint_joinPoint y 0⟩
  obtain ⟨δ', hδ', hball⟩ := exists_controlDistance_lt_of_euclid_close C hmem hε
  refine ⟨δ', hδ', fun y' hy' => ?_⟩
  obtain ⟨⟨ξ, hξ, rfl⟩, hd⟩ := hball y' hy'
  exact ⟨liftedChart_basePoint_mem C hξ, hd⟩

/-- **A continuous representative with intrinsic derivatives,
Hölder case, under a `LocalSolvability` hypothesis.** Under the hypotheses of `smoothing_holder_of_localSolvability`
(without `hdbl`): `T` is the distribution of a function `F` continuous on `Ω`, and every word `X_I F`
of weight at most two exists as a continuous weak derivative, hence as the intrinsic
derivative, on all of `Ω`. The local continuous representatives of the cylinder descent glue
(`exists_continuous_gluing`), the local continuous weak word derivatives glue
(`exists_continuous_hasWeakWordDeriv_gluing`), and continuous weak derivatives are intrinsic
(`hasIntrinsicWordDeriv_of_continuous_weak_words`; BB pp. 609-610). -/
theorem exists_continuous_representative_of_localSolvability (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hchart : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m))
    (hSolv : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m), LocalSolvability C)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ)
    (hf : memHolderX driftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) Ω 0 α f)
    (hT : hasDistributionEquationWithDrift Ω X hX T f) :
    ∃ F : (Fin n → ℝ) → ℝ, ContinuousOn F (Ω : Set (Fin n → ℝ)) ∧
      T = Distribution.ofFun Ω F volume (⊤ : ℕ∞) ∧
      ∀ I ∈ wordFamily driftWeight 2, ∃ g : (Fin n → ℝ) → ℝ,
        ContinuousOn g (Ω : Set (Fin n → ℝ)) ∧ hasWeakWordDeriv X Ω I F g ∧
          hasIntrinsicWordDeriv X Ω I F g := by
  classical
  have hlocal : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ A : Opens (Fin n → ℝ),
      x₀ ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ Ω ∧ ∃ u : (Fin n → ℝ) → ℝ,
        representsDistribution A (RothschildStein.S.distributionRestrictionCLM Ω A T) u ∧
          ContinuousOn u (A : Set (Fin n → ℝ)) ∧
          ∀ I ∈ wordFamily driftWeight 2, ∃ g : (Fin n → ℝ) → ℝ,
            hasWeakWordDeriv X A I u g ∧ ContinuousOn g (A : Set (Fin n → ℝ)) := by
    intro x₀ hx₀
    obtain ⟨s, m, ⟨C⟩⟩ := hchart x₀ hx₀
    exact exists_local_representative_holder_of_localSolvability C (hSolv x₀ s m C) hα hα1 T hf hT
  choose! A hxA hAΩ u hrep huc hweak using hlocal
  have hcover : ∀ x ∈ (Ω : Set (Fin n → ℝ)), ∃ i : Ω, x ∈ (A i : Set (Fin n → ℝ)) :=
    fun x hx => ⟨⟨x, hx⟩, hxA x hx⟩
  obtain ⟨F, hFc, hTF, hFeq⟩ := exists_continuous_gluing Ω T (fun x : Ω => A x) (fun x => u x)
    (fun x => hAΩ x x.2) hcover (fun x => huc x x.2)
    (fun x ψ hψ => integral_eq_of_representsDistribution Ω (A x) (hAΩ x x.2) T (hrep x x.2) ψ hψ)
  have hFloc : LocallyIntegrableOn F (Ω : Set (Fin n → ℝ)) volume :=
    hFc.locallyIntegrableOn Ω.isOpen.measurableSet
  have hglob : ∀ I ∈ wordFamily driftWeight 2, ∃ G : (Fin n → ℝ) → ℝ,
      ContinuousOn G (Ω : Set (Fin n → ℝ)) ∧ hasWeakWordDeriv X Ω I F G := by
    intro I hI
    choose g hg hgc using fun x : Ω => hweak x x.2 I hI
    have hgF : ∀ x : Ω, hasWeakWordDeriv X (A x) I F (g x) := fun x =>
      RothschildStein.S.hasWeakWordDeriv_congr_ae X (A x) (hg x)
        ((ae_restrict_iff' (A x).isOpen.measurableSet).2
          (Eventually.of_forall fun y hy => (hFeq x hy).symm)) Filter.EventuallyEq.rfl
    obtain ⟨G, hGc, hG, -⟩ := exists_continuous_hasWeakWordDeriv_gluing X Ω hX I hFloc
      (fun x : Ω => A x) (fun x => hAΩ x x.2) hcover g hgF hgc
    exact ⟨G, hGc, hG⟩
  let jet : List (Fin (q + 1)) → (Fin n → ℝ) → ℝ := fun J =>
    if h : J ∈ wordFamily driftWeight 2 then
      (if J = [] then F else Classical.choose (hglob J h)) else 0
  have hjet0 : jet [] = F := by
    simp [jet, RothschildStein.S.nil_mem_wordFamily]
  have hjetW : ∀ J ∈ wordFamily driftWeight 2,
      hasWeakWordDeriv X Ω J F (jet J) ∧ ContinuousOn (jet J) (Ω : Set (Fin n → ℝ)) := by
    intro J hJ
    by_cases hJ0 : J = []
    · subst hJ0
      rw [hjet0]
      exact ⟨RothschildStein.S.hasWeakWordDeriv_nil X Ω hFloc, hFc⟩
    · have hj : jet J = Classical.choose (hglob J hJ) := by simp [jet, hJ, hJ0]
      rw [hj]
      exact ⟨(Classical.choose_spec (hglob J hJ)).2, (Classical.choose_spec (hglob J hJ)).1⟩
  refine ⟨F, hFc, hTF, fun I hI => ⟨jet I, (hjetW I hI).2, (hjetW I hI).1, ?_⟩⟩
  exact hasIntrinsicWordDeriv_of_continuous_weak_words Ω X hX I F jet hjet0
    (fun J hJ => (hjetW J (RothschildStein.S.sublist_mem_wordFamily driftWeight 2 hJ hI)).1)
    (fun J hJ => (hjetW J (RothschildStein.S.sublist_mem_wordFamily driftWeight 2 hJ hI)).2)

/-- **The Hölder norm of the glued representative on a base control ball.**
Let `F` be a continuous representative of `T` with intrinsic word derivatives on `Ω` (as supplied by
`exists_continuous_representative_of_localSolvability`), `C` a lifted chart at `x₀` and
`OriginalLocalDoubling` the local doubling on the projected chart neighborhood. Then there is a base
control ball `A = B(x₀, δ t) ∋ x₀` with `F ∈ C^{2,α}_X(A)` (`memHolderX`).

The lift `F ∘ π` represents `T̃` on every lifted control ball, so it agrees on it with the continuous
representative `w = v + H` of `solve_subtract_holder_of_localSolvability` (two continuous functions with
the same distribution: `Distribution.ofFun_injective`, everywhere equal, BB p. 610 "identified
lifts"); `w ∈ C^{2,α}_{X̃}` on the relatively compact ball `U_s`, and the reverse Hölder transfer
(`holderTransfer_of_doubling`) bounds the base norm on `B(x₀, δ t)` by the lifted norm on `U_s`. -/
theorem memHolderX_near_point_of_localSolvability (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hchart : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m))
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ (Ω : Set (Fin n → ℝ))) {s m : ℕ}
    (C : P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m) (hP : LocalSolvability C)
    (hdbl : OriginalLocalDoubling (Ω : Set (Fin n → ℝ)) driftWeight X (basePoint '' C.U))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ)
    (hf : memHolderX driftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) Ω 0 α f)
    (hT : hasDistributionEquationWithDrift Ω X hX T f)
    {F : (Fin n → ℝ) → ℝ} (hFc : ContinuousOn F (Ω : Set (Fin n → ℝ)))
    (hTF : T = Distribution.ofFun Ω F volume (⊤ : ℕ∞))
    (hglobI : ∀ I ∈ wordFamily driftWeight 2, ∃ g : (Fin n → ℝ) → ℝ,
      hasIntrinsicWordDeriv X Ω I F g) :
    ∃ A : Opens (Fin n → ℝ), x₀ ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ Ω ∧
      memHolderX driftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) A 2 α F := by
  have hξ₀ : joinPoint x₀ (0 : Fin m → ℝ) ∈ C.U := C.center_mem
  obtain ⟨UR, hξUR, hURU, w, hwc, hrepr, hSob⟩ :=
    solve_subtract_holder_of_localSolvability C hP hα hα1 T hf hT hξ₀
  -- `w` and `F ∘ π` are continuous representatives of the lift on `UR`: they agree
  have hFπc : ContinuousOn (fun ξ => F (basePoint ξ)) (UR : Set (Fin (n + m) → ℝ)) :=
    hFc.comp continuous_basePoint.continuousOn (fun ξ hξ => liftedChart_basePoint_mem C (hURU hξ))
  have hFπloc : LocallyIntegrableOn (fun ξ => F (basePoint ξ))
      (liftedChartOpens C : Set (Fin (n + m) → ℝ)) volume :=
    (hFc.comp continuous_basePoint.continuousOn
      (fun ξ hξ => liftedChart_basePoint_mem C hξ)).locallyIntegrableOn
      (liftedChartOpens C).isOpen.measurableSet
  have hFloc : LocallyIntegrableOn F (Ω : Set (Fin n → ℝ)) volume :=
    hFc.locallyIntegrableOn Ω.isOpen.measurableSet
  have hlift : liftedChartLift C T =
      Distribution.ofFun (liftedChartOpens C) (fun ξ => F (basePoint ξ)) volume (⊤ : ℕ∞) := by
    rw [hTF]
    exact liftedChartLift_ofFun C hFloc
  have hres : RothschildStein.S.distributionRestrictionCLM (liftedChartOpens C) UR
      (liftedChartLift C T) =
      Distribution.ofFun UR (fun ξ => F (basePoint ξ)) volume (⊤ : ℕ∞) := by
    rw [hlift]
    exact distributionRestriction_ofFun (liftedChartOpens C) UR hURU hFπloc
  have hae : w =ᵐ[volume.restrict (UR : Set (Fin (n + m) → ℝ))] fun ξ => F (basePoint ξ) :=
    Distribution.ofFun_injective (hwc.locallyIntegrableOn UR.isOpen.measurableSet)
      (hFπc.locallyIntegrableOn UR.isOpen.measurableSet) (hrepr.symm.trans hres)
  have hweq : EqOn w (fun ξ => F (basePoint ξ)) (UR : Set (Fin (n + m) → ℝ)) :=
    Measure.eqOn_open_of_ae_eq hae UR.isOpen hwc hFπc
  -- a small lifted control ball with compact closure in `UR`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp UR.isOpen _ hξUR
  have hK₁sub : Metric.closedBall (joinPoint x₀ (0 : Fin m → ℝ)) (ε / 2) ⊆ UR :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK₁ : IsCompact (Metric.closedBall (joinPoint x₀ (0 : Fin m → ℝ)) (ε / 2)) :=
    isCompact_closedBall _ _
  obtain ⟨rstar₁, hr₁⟩ := P1.LiftedChart.exists_isSmallBallRadius (C := C) hK₁
    (hK₁sub.trans hURU)
    (Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (half_pos hε)))
  obtain ⟨-, rstar₂, δ, hr₂, hδ0, hδ1, hP7⟩ := holderTransfer_of_doubling C hα hα1
    (K := {joinPoint x₀ (0 : Fin m → ℝ)}) isCompact_singleton (singleton_subset_iff.2 hξ₀) hdbl
  have hmin : 0 < min rstar₁ rstar₂ / 2 := half_pos (lt_min hr₁.pos hr₂)
  have hs₁ : min rstar₁ rstar₂ / 2 < rstar₁ := by
    have := min_le_left rstar₁ rstar₂; linarith [hr₁.pos]
  have hs₂ : min rstar₁ rstar₂ / 2 < rstar₂ := by
    have := min_le_right rstar₁ rstar₂; linarith
  set s' := min rstar₁ rstar₂ / 2 with hs'
  obtain ⟨Cst, hCst, hC⟩ := hP7 (s' / 2) s' (half_pos hmin) (by linarith) hs₂
  obtain ⟨-, hCw⟩ := hC (joinPoint x₀ (0 : Fin m → ℝ)) (mem_singleton _)
  let Us : Opens (Fin (n + m) → ℝ) :=
    ⟨rsBall C.O driftWeight C.Xl (joinPoint x₀ (0 : Fin m → ℝ)) s',
      isOpen_rsBall_of_isSmallBallRadius C hr₁ hmin hs₁⟩
  let Vs : Opens (Fin n → ℝ) :=
    ⟨rsBall (Ω : Set (Fin n → ℝ)) driftWeight X (basePoint (joinPoint x₀ (0 : Fin m → ℝ))) s',
      isOpen_rsBall_base Ω X hchart _ _⟩
  let Vδ : Opens (Fin n → ℝ) :=
    ⟨rsBall (Ω : Set (Fin n → ℝ)) driftWeight X (basePoint (joinPoint x₀ (0 : Fin m → ℝ)))
      (δ * (s' / 2)), isOpen_rsBall_base Ω X hchart _ _⟩
  have hUsK : (Us : Set (Fin (n + m) → ℝ)) ⊆ Metric.closedBall (joinPoint x₀ (0 : Fin m → ℝ)) (ε / 2) :=
    hr₁.ball_subset s' hmin hs₁
  have hclK : closure (Us : Set (Fin (n + m) → ℝ)) ⊆
      Metric.closedBall (joinPoint x₀ (0 : Fin m → ℝ)) (ε / 2) :=
    closure_minimal hUsK Metric.isClosed_closedBall
  have hmemUs : memHolderX driftWeight C.Xl C.dl Us 2 α w :=
    hSob Us (hK₁.of_isClosed_subset isClosed_closure hclK) (hclK.trans hK₁sub)
  have hlift_fin : holderXENorm driftWeight C.Xl C.dl Us 2 α (fun ξ => F (basePoint ξ)) < ⊤ :=
    holderXENorm_lt_top_of_memHolderX_congr driftWeight C.Xl C.dl Us hmemUs
      (fun ξ hξ => (hweq (hK₁sub (hUsK hξ))).symm)
  have hVsΩ : (Vs : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := fun y hy => hy.1
  have hderiv : ∀ I ∈ wordFamily driftWeight 2, ∃ g : (Fin n → ℝ) → ℝ,
      hasIntrinsicWordDeriv X Vs I F g := fun I hI => by
    obtain ⟨g, hg⟩ := hglobI I hI
    exact ⟨g, hasIntrinsicWordDeriv_mono hVsΩ I hg⟩
  have key := hCw Vδ Vs Us rfl rfl rfl 2 F hderiv
  have hfin : holderXENorm driftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X)
      Vδ 2 α F < ⊤ :=
    lt_of_le_of_lt key (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlift_fin)
  refine ⟨Vδ, ?_, fun y hy => hy.1, memHolderX_of_holderXENorm_lt_top driftWeight X _ Vδ hfin⟩
  refine ⟨hx₀, ?_⟩
  rw [basePoint_joinPoint, G1.controlDistance_self _ X hx₀]
  exact ENNReal.ofReal_pos.2 (mul_pos hδ0 (half_pos hmin))

/-- **Distributional smoothing, Hölder case (BB Thm 11.62, pp. 608-610), under a `LocalSolvability` hypothesis and the local doubling hypothesis.** Let `Ω ⊆ ℝⁿ` be open, `X = (X₀, …, X_q)` smooth fields on `Ω` (`X₀` the drift),
`T ∈ 𝒟'(Ω)` with `L T = f` and `f ∈ C^α_X(Ω)`, `0 < α < 1` (`memHolderX` of order `0` for the
control distance of `Ω`). Then `T` has a representative `u`, continuous on `Ω`, such that

* every word derivative `X_I u`, `I` of weight at most `2`, exists on `Ω` as a continuous (weak and
  intrinsic) derivative, and
* `u ∈ C^{2,α}_X(A)` (`memHolderX`) on a base control ball `A ∋ x₀`, `A ⊆ Ω`, around every
  point `x₀ ∈ Ω`.

This is the statement `u ∈ C^{2,α}_{X,loc}(Ω)` in the local-neighborhood form of BB p. 610 ("near each
point"). The passage from the balls `A` to every relatively compact `V ⋐ Ω` (`memHolderXLoc`) is the finite-cover argument of the base Hölder estimate; it is
`holderENorm_lt_top_of_local_balls` in `SmoothingTheoremCover` (the Hölder seminorm is a supremum
over all pairs of `V`, so covering needs the control geometry `HD1`-`HD2` of `Ω`, which that file
derives from the lifted charts).

Hypotheses: `hchart` is the conclusion of the lifting theorem `exists_lift_approximation_drift` at
every point (a lifted chart, `liftedChart_of_drift`); `hSolv` is local solvability for every lifted chart;
`hdbl` is the compact-centre local doubling on each projected chart neighborhood (as in
`holderTransfer_of_doubling`). -/
theorem smoothing_holder_of_localSolvability (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hchart : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m))
    (hSolv : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m), LocalSolvability C)
    (hdbl : ∀ (x₀ : Fin n → ℝ) (s m : ℕ)
      (C : P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m),
      OriginalLocalDoubling (Ω : Set (Fin n → ℝ)) driftWeight X (basePoint '' C.U))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ)
    (hf : memHolderX driftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) Ω 0 α f)
    (hT : hasDistributionEquationWithDrift Ω X hX T f) :
    ∃ u : (Fin n → ℝ) → ℝ, LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
      T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧ ContinuousOn u (Ω : Set (Fin n → ℝ)) ∧
      (∀ I ∈ wordFamily driftWeight 2, ∃ g : (Fin n → ℝ) → ℝ,
        ContinuousOn g (Ω : Set (Fin n → ℝ)) ∧ hasWeakWordDeriv X Ω I u g ∧
          hasIntrinsicWordDeriv X Ω I u g) ∧
      ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ A : Opens (Fin n → ℝ), x₀ ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ Ω ∧
        memHolderX driftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) A 2 α u := by
  obtain ⟨F, hFc, hTF, hglob⟩ :=
    exists_continuous_representative_of_localSolvability Ω X hX hchart hSolv hα hα1 T f hf hT
  refine ⟨F, hFc.locallyIntegrableOn Ω.isOpen.measurableSet, hTF, hFc, hglob, fun x₀ hx₀ => ?_⟩
  obtain ⟨s, m, ⟨C⟩⟩ := hchart x₀ hx₀
  exact memHolderX_near_point_of_localSolvability Ω X hX hchart hx₀ C (hSolv x₀ s m C)
    (hdbl x₀ s m C) hα hα1 T f hf hT hFc hTF
    (fun I hI => by obtain ⟨g, -, -, hg⟩ := hglob I hI; exact ⟨g, hg⟩)

end Hölder

end RothschildStein.P2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingNoDriftStatement
public import RothschildStein.P2.SmoothingSolveEquation
public import RothschildStein.P1.RightParametrixNoDriftPairing

/-!
# Lift, solve and subtract without drift: the abstract part

The no-drift counterpart of the equation lemmas of `SmoothingSolveEquation` (`hasDistributionEquation`, `L = ∑ Xᵢ²`, fields `Fin q`):

* `hasDistributionEquation_ofFun_of_weakNoDriftEquation` (the weak-derivative definition, for `v ∈ W^{2,p}`): a weak solution
  is a distributional solution;
* `hasDistributionEquation_restrict_noDrift`: the distributional equation restricts to a smaller
  open set (`L` is local);
* `exists_smooth_add_of_hasDistributionEquation_noDrift` (abstract solve-subtract): if `T ∈ 𝒟'(V)`
  has `L T = f`, `v` solves `L v = g` weakly, `f = g` a.e. and the fields satisfy the Hörmander
  condition on `V`, then `T = v + H` with `H` smooth on `V` (`H = T - v` solves `L H = 0`, the homogeneous hypoellipticity statement,
  `exists_smooth_representative_of_hasDistributionEquation`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section NoDriftEquations

variable {n q : ℕ}

/-- The right-hand side of a weak no-drift equation is locally integrable on `V`. -/
theorem weakNoDriftEquation.locallyIntegrableOn {V : Opens (Fin n → ℝ)}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {v g : (Fin n → ℝ) → ℝ}
    (h : weakNoDriftEquation V X v g) : LocallyIntegrableOn g (V : Set (Fin n → ℝ)) volume := by
  obtain ⟨gs, hs, hae⟩ := h
  have hsum : LocallyIntegrableOn (fun x => ∑ i, gs i x) (V : Set (Fin n → ℝ)) volume :=
    locallyIntegrableOn_finsetSum Finset.univ (fun i _ => (hs i).2.1)
  exact hsum.congr hae

/-- A weak solution is a distributional solution: if every `Xᵢ Xᵢ v` exists as a weak word
derivative on `V` and `∑ XᵢXᵢ v = g` a.e., then the distribution of `v` satisfies the distributional equation `L (ofFun v) = g` (BB p. 67-68, Def 2.1), `L = ∑ Xᵢ²`. -/
theorem hasDistributionEquation_ofFun_of_weakNoDriftEquation (V : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {v g : (Fin n → ℝ) → ℝ} (hv : weakNoDriftEquation V X v g) :
    hasDistributionEquation V X hX (Distribution.ofFun V v volume (⊤ : ℕ∞)) g := by
  have hg := hv.locallyIntegrableOn
  obtain ⟨gs, hs, hae⟩ := hv
  refine ⟨hg, fun φ => ?_⟩
  have e1 : ∀ i : Fin q, Distribution.ofFun V v volume (⊤ : ℕ∞)
      (fieldTransposeTest V (X i) (hX i) (fieldTransposeTest V (X i) (hX i) φ)) =
        Distribution.ofFun V (gs i) volume (⊤ : ℕ∞) φ := by
    intro i
    have := congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
      (RothschildStein.S.distributionWord_ofFun_eq V X hX [i, i] v (gs i) (hs i))
    simp only [RothschildStein.S.distributionWordCLM_apply,
      fieldTransposeTest_comp_eq_wordTransposeTest_pair] at this
    exact this
  have hcongr := congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
    (Distribution.ofFun_congr_ae (Ω := V) (n := (⊤ : ℕ∞)) (μ := volume) hae)
  unfold sumSquaresTransposeTest
  rw [map_sum]
  simp_rw [e1]
  rw [← ofFun_finsetSum_apply Finset.univ (fun i _ => (hs i).2.1)]
  exact hcongr

/-- The distributional no-drift equation restricts to a smaller open set (`L` is local). -/
theorem hasDistributionEquation_restrict_noDrift (V U : Opens (Fin n → ℝ)) (hUV : U ≤ V)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {T : Distribution V ℝ (⊤ : ℕ∞)} {f : (Fin n → ℝ) → ℝ}
    (hT : hasDistributionEquation V X hX T f) :
    hasDistributionEquation U X (fun i => (hX i).mono hUV)
      (RothschildStein.S.distributionRestrictionCLM V U T) f := by
  refine ⟨hT.1.mono_set hUV, fun φ => ?_⟩
  let φ' : TestFunction V ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hUV⟩
  have hcoe : (sumSquaresTransposeTest U X (fun i => (hX i).mono hUV) φ :
      (Fin n → ℝ) → ℝ) = sumSquaresTranspose X φ :=
    P1.sumSquaresTransposeTest_coe_noDrift U X _ φ
  have hcoe' : (sumSquaresTransposeTest V X hX φ' : (Fin n → ℝ) → ℝ) =
      sumSquaresTranspose X φ' :=
    P1.sumSquaresTransposeTest_coe_noDrift V X hX φ'
  rw [RothschildStein.S.distributionRestrictionCLM_apply V U hUV T]
  have hmem : (⟨(sumSquaresTransposeTest U X (fun i => (hX i).mono hUV) φ :
      (Fin n → ℝ) → ℝ), (sumSquaresTransposeTest U X (fun i => (hX i).mono hUV) φ).contDiff,
      (sumSquaresTransposeTest U X (fun i => (hX i).mono hUV) φ).hasCompactSupport,
      (sumSquaresTransposeTest U X (fun i => (hX i).mono hUV) φ).tsupport_subset.trans
        hUV⟩ : TestFunction V ℝ (⊤ : ℕ∞)) = sumSquaresTransposeTest V X hX φ' := by
    apply TestFunction.ext
    intro x
    change (sumSquaresTransposeTest U X (fun i => (hX i).mono hUV) φ :
      (Fin n → ℝ) → ℝ) x = (sumSquaresTransposeTest V X hX φ' : (Fin n → ℝ) → ℝ) x
    rw [hcoe, hcoe']
    rfl
  rw [hmem, hT.2 φ', Distribution.ofFun_apply hT.1, Distribution.ofFun_apply (hT.1.mono_set hUV)]
  rfl

/-- Let `V` be open, the fields smooth on `V` with
the Hörmander rank condition `bracketSpansOn V X`, `T ∈ 𝒟'(V)` with `L T = f`, `L = ∑ Xᵢ²`, and `v`
a locally integrable weak solution of `L v = g` on `V` with `f = g` a.e. Then `H = T - v` solves
`L H = 0` distributionally, so by the homogeneous hypoellipticity statement it is a smooth function `h`, and `T` is the regular
distribution of `v + h` (BB p. 609-610: `T = v + H`). -/
theorem exists_smooth_add_of_hasDistributionEquation_noDrift (V : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (V : Set (Fin n → ℝ)) X) (T : Distribution V ℝ (⊤ : ℕ∞))
    {f v g : (Fin n → ℝ) → ℝ} (hT : hasDistributionEquation V X hX T f)
    (hvloc : LocallyIntegrableOn v (V : Set (Fin n → ℝ)) volume)
    (hv : weakNoDriftEquation V X v g)
    (hfg : f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] g) :
    ∃ h : (Fin n → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) h (V : Set (Fin n → ℝ)) ∧
      T = Distribution.ofFun V (fun x => v x + h x) volume (⊤ : ℕ∞) := by
  have hDv := hasDistributionEquation_ofFun_of_weakNoDriftEquation V X hX hv
  have hH : hasDistributionEquation V X hX
      (T - Distribution.ofFun V v volume (⊤ : ℕ∞)) 0 := by
    refine ⟨locallyIntegrableOn_zero, fun φ => ?_⟩
    have h1 := hT.2 φ
    have h2 := hDv.2 φ
    have h3 : Distribution.ofFun V f volume (⊤ : ℕ∞) φ =
        Distribution.ofFun V g volume (⊤ : ℕ∞) φ :=
      congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
        (Distribution.ofFun_congr_ae (Ω := V) (n := (⊤ : ℕ∞)) (μ := volume) hfg)
    have h4 : (T - Distribution.ofFun V v volume (⊤ : ℕ∞))
        (sumSquaresTransposeTest V X hX φ) =
        T (sumSquaresTransposeTest V X hX φ) -
          Distribution.ofFun V v volume (⊤ : ℕ∞) (sumSquaresTransposeTest V X hX φ) := rfl
    rw [h4, h1, h2, h3, sub_self]
    have : Distribution.ofFun V (0 : (Fin n → ℝ) → ℝ) volume (⊤ : ℕ∞) = 0 :=
      Distribution.ofFun_zero
    rw [this]
    rfl
  obtain ⟨h, hsm, hHeq, -⟩ :=
    exists_smooth_representative_of_hasDistributionEquation V X hX hspan _ hH
  refine ⟨h, hsm, ?_⟩
  have hhloc : LocallyIntegrableOn h (V : Set (Fin n → ℝ)) volume :=
    hsm.continuousOn.locallyIntegrableOn V.isOpen.measurableSet
  have hsum := Distribution.ofFun_add (Ω := V) (n := (⊤ : ℕ∞)) (μ := volume) hvloc hhloc
  have : T = Distribution.ofFun V v volume (⊤ : ℕ∞) +
      (T - Distribution.ofFun V v volume (⊤ : ℕ∞)) := by abel
  rw [this, hHeq]
  exact hsum.symm

end NoDriftEquations

end RothschildStein.P2

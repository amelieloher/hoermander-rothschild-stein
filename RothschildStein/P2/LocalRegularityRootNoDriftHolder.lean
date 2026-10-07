-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityPaddingHolder
public import RothschildStein.P2.LocalRegularityCoreNoDrift

/-!
# Local regularity without drift, Hölder (BB Thm 11.1): the root `rs3_no_drift_holder_of_hypotheses`

The regularity argument for the padded system without drift: the no-drift chain (`rs3_no_drift_holder_core`, a system of
dimension `n + 3 ≥ 3`) is applied to the padded system on `Ω × B₃`, and the result descends
(the reduction to dimension at least three by padding): the continuous representative `uP` is independent of the fiber
(`slice_eq_of_continuous`), `u = uP(·, 0)` represents `T` on `Ω`, every original intrinsic word
derivative restricts to the slice with constant one (`memHolderX_paddingNoDrift_ambient_slice`,
`holderXENorm_paddingNoDrift_ambient_slice_le`), the data norm pulls back with constant one
(`holderXENorm_paddingNoDrift_pullback_le`), the sup norm of `uP` on `W × B₂` is that of `u` on `W`, and
the pointwise padded equation `∑ᵢ gᵢ + ∑ⱼ ∂_{z_j}² uP = f` loses its added terms
(`eqOn_zero_of_added_pair_noDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- BB Thm 11.1 (no drift, all `k`, Hölder): the statement of
`RothschildStein.rs3_no_drift_holder`, assuming the upstream bundle `U`
(`NoDriftHolderHypotheses`: the lifting theorem statement, left differentiation `LeftDifferentiation` (which gives local solvability), the local doubling property and the higher Hölder estimate in dimension
`≥ 3`). -/
theorem rs3_no_drift_holder_of_hypotheses (U : NoDriftHolderHypotheses)
    {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
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
  -- fibers, cylinders, the padded system
  have hJ3pos := volume_fiberBall_pos (r := 3) (by norm_num)
  have hJ3top := volume_fiberBall_lt_top 3
  set J₁ := fiberBall 1 with hJ₁
  set J₂ := fiberBall 2 with hJ₂
  set J₃ := fiberBall 3 with hJ₃
  have hJ12 : closure (J₁ : Set (Fin 3 → ℝ)) ⊆ (J₂ : Set (Fin 3 → ℝ)) :=
    closure_fiberBall_subset (by norm_num)
  have hJ23 : closure (J₂ : Set (Fin 3 → ℝ)) ⊆ (J₃ : Set (Fin 3 → ℝ)) :=
    closure_fiberBall_subset (by norm_num)
  have hJ1c : IsCompact (closure (J₁ : Set (Fin 3 → ℝ))) := isCompact_closure_fiberBall 1
  have hJ2c : IsCompact (closure (J₂ : Set (Fin 3 → ℝ))) := isCompact_closure_fiberBall 2
  have hz1 : (0 : Fin 3 → ℝ) ∈ (J₁ : Set (Fin 3 → ℝ)) := zero_mem_fiberBall one_pos
  have hz2 : (0 : Fin 3 → ℝ) ∈ (J₂ : Set (Fin 3 → ℝ)) := zero_mem_fiberBall two_pos
  have hz3 : (0 : Fin 3 → ℝ) ∈ (J₃ : Set (Fin 3 → ℝ)) := zero_mem_fiberBall (by norm_num)
  have hWΩ' : (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hWΩ
  have hVΩ' : (V : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans (hVW.trans hWΩ')
  let XP : Fin (q + 3) → (Fin (n + 3) → ℝ) → (Fin (n + 3) → ℝ) :=
    paddingNoDriftVectorFields (d := 3) X
  have hXP : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (XP i) (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) :=
    contDiffOn_paddingNoDriftVectorFields_projection (Ω : Set (Fin n → ℝ))
      (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) (padding_cylinder_subset_base Ω J₃) X hX
  have hspanP := bracketSpansOn_paddingNoDrift (d := 3) Ω J₃ X hX hspan
  obtain ⟨CP, hCP, hcore⟩ := rs3_no_drift_holder_core U (n := n + 3) (q := q + 3) (by omega)
    (by omega) (cylinder Ω J₃) (cylinder V J₁) (cylinder W J₂)
    (isCompact_closure_cylinder hV hJ1c) (closure_cylinder_subset hVW hJ12)
    (isCompact_closure_cylinder hW hJ2c) (closure_cylinder_subset hWΩ hJ23)
    XP hXP hspanP k α hα hα1
  refine ⟨CP, hCP, fun T f hf hT => ?_⟩
  have hfloc : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume := hT.1
  have hw : paddingNoDriftWeights (d := 3) (noDriftWeight : Fin q → ℕ+) =
      (noDriftWeight : Fin (q + 3) → ℕ+) := paddingNoDriftWeights_noDriftWeight
  -- the data is continuous on `Ω`, so its pullback is locally integrable on the cylinder
  have hchart := hchart_noDrift U.liftApproximation hn hq Ω X hX hspan
  have hfc : ContinuousOn f (Ω : Set (Fin n → ℝ)) :=
    continuousOn_of_holderENorm_charts hchart hα hf.1
  -- the padded data
  have hfP : memHolderX noDriftWeight XP
      (controlDistance (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) noDriftWeight XP)
      (cylinder Ω J₃) k α (fun ξ => f (basePoint ξ)) := by
    have := memHolderX_paddingNoDrift_lift Ω J₃ Ω J₃ noDriftWeight X hX α hα.le f hf
    rwa [hw] at this
  have hTP : hasDistributionEquation (cylinder Ω J₃) XP hXP
      (paddingDistributionTensorOneCLM Ω (cylinder Ω J₃) (padding_cylinder_subset_base Ω J₃) T)
      (fun ξ => f (basePoint ξ)) := by
    refine ⟨locallyIntegrableOn_comp_basePoint_cylinder Ω J₃ hfc, fun φ => ?_⟩
    have h1 := paddingDistributionTensor_noDrift_equation Ω (cylinder Ω J₃)
      (padding_cylinder_subset_base Ω J₃) X hX T (Distribution.ofFun Ω f volume (⊤ : ℕ∞)) hT.2 φ
    rw [paddingDistributionTensorOneCLM_ofFun Ω J₃ hJ3top.ne f hfloc] at h1
    exact h1
  obtain ⟨uP, huPloc, hTuP, huPc, huPLoc, hest, gP, hgP, hgPeq⟩ := hcore (paddingDistributionTensorOneCLM Ω (cylinder Ω J₃) (padding_cylinder_subset_base Ω J₃) T) _ hfP hTP
  -- the descended function: the slice at `z = 0`
  set η₃ := fiberBump 3 (by norm_num) with hη₃
  have hη3 : ∫ z, η₃ z = 1 := fiberBump_integral 3 _
  have hindep : ∀ ξ ∈ (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)),
      uP ξ = uP (joinPoint (basePoint ξ) 0) := by
    intro ξ hξ
    have := slice_eq_of_continuous Ω J₃ hJ3top.ne η₃ hη3 T uP huPloc hTuP huPc hξ.1 hξ.2 hz3
    rwa [joinPoint_basePoint_tailPoint ξ] at this
  set u : (Fin n → ℝ) → ℝ := fun x => uP (joinPoint x 0) with hu
  have hrep : representsDistribution Ω T u :=
    paddingDistributionTensor_continuous_slice_represents Ω J₃ hJ3top.ne η₃ hη3 T uP huPloc hTuP
      huPc 0 hz3
  have huc : ContinuousOn u (Ω : Set (Fin n → ℝ)) := continuousOn_slice Ω J₃ hz3 huPc
  have huPu : ∀ ξ ∈ (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)), uP ξ = u (basePoint ξ) := hindep
  refine ⟨u, hrep.1, hrep.2, huc, fun V' hV'c hV'Ω => ?_, ?_, ?_⟩
  · -- order `k + 2` on `V' ⋐ Ω`: the slice of the padded Hölder membership on `V' × B₂`
    have hV'Ω' : (V' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hV'Ω
    have hSob : memHolderX noDriftWeight XP
        (controlDistance (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) noDriftWeight XP)
        (cylinder V' J₂) (k + 2) α uP :=
      huPLoc _ (isCompact_closure_cylinder hV'c hJ2c) (closure_cylinder_subset hV'Ω hJ23)
    rw [← hw] at hSob
    exact memHolderX_paddingNoDrift_ambient_slice Ω J₃ V' J₂ noDriftWeight X
      (fun i => (hX i).mono hV'Ω') α uP hSob 0 hz3 hz2
  · -- the estimate on `V ⋐ W`
    have hs := holderXENorm_paddingNoDrift_ambient_slice_le (k := k + 2) Ω J₃ V J₁ noDriftWeight X
      (fun i => (hX i).mono hVΩ') α uP 0 hz3 hz1
    have hfW : memHolderX noDriftWeight X d W k α f :=
      memHolderX_mono_domain noDriftWeight hWΩ' hf
    have hfPW := holderXENorm_paddingNoDrift_pullback_le (k := k) Ω J₃ W J₂ noDriftWeight X
      (fun i => (hX i).mono hWΩ') α hα.le f hfW
    rw [hw] at hs hfPW
    have hsup := eLpNorm_top_cylinder_le W J₂ u uP fun ξ hξ => huPu ξ (cylinder_subset
      (hWΩ' : W ≤ Ω) (fiberBall_mono (by norm_num)) hξ)
    calc holderXENorm noDriftWeight X d V (k + 2) α u
        ≤ holderXENorm noDriftWeight XP
            (controlDistance (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) noDriftWeight XP)
            (cylinder V J₁) (k + 2) α uP := hs
      _ ≤ ENNReal.ofReal CP * (holderXENorm noDriftWeight XP
            (controlDistance (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) noDriftWeight XP)
            (cylinder W J₂) k α (fun ξ => f (basePoint ξ)) +
            eLpNorm uP ⊤ (volume.restrict (cylinder W J₂ : Set (Fin (n + 3) → ℝ)))) := hest
      _ ≤ ENNReal.ofReal CP * (holderXENorm noDriftWeight X d W k α f +
            eLpNorm u ⊤ (volume.restrict (W : Set (Fin n → ℝ)))) := by gcongr
  · -- the strong equation: the added terms vanish
    refine ⟨fun i x => gP (Fin.castAdd 3 i) (joinPoint x 0), fun i => ?_, fun x hx => ?_⟩
    · exact hasIntrinsicWordDeriv_paddingNoDrift_map_slice Ω J₃ X hX [i, i] uP
        (gP (Fin.castAdd 3 i)) (hgP (Fin.castAdd 3 i)) 0 hz3
    · have hξ : joinPoint x 0 ∈ (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) :=
        joinPoint_mem_cylinder.2 ⟨hx, hz3⟩
      have h1 := hgPeq _ hξ
      rw [Fin.sum_univ_add] at h1
      have hadd : ∀ j : Fin 3, gP (Fin.natAdd q j) (joinPoint x 0) = 0 := fun j =>
        eqOn_zero_of_added_pair_noDrift Ω J₃ X hX u uP _ j huPu (hgP (Fin.natAdd q j)) hξ
      simp only [hadd, Finset.sum_const_zero, add_zero, basePoint_joinPoint] at h1
      exact h1

end RothschildStein.P2

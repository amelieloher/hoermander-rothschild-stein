-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityPaddingSetup
public import RothschildStein.P2.LocalRegularityCoreNoDrift

/-!
# Local regularity without drift, `L^p` (BB Thm 11.1): the root `rs3_no_drift_sobolev_of_hypotheses`

The regularity argument for the padded system without drift: the no-drift chain (`rs3_no_drift_sobolev_core`, a system of
dimension `n + 3 ≥ 3`) is applied to the padded system on `Ω × B₃`, and the result descends
(the reduction to dimension at least three by padding): `u = ∫ uP(·, z) η(z) dz` represents `T` on `Ω`, lies in
`W^{k+2,p}_{X,loc}(Ω)` (`paddingDistributionTensor_noDrift_sobolev_descent` on `V' × B₂`) and
`|B₁|^{1/p} ‖u‖_{W^{k+2,p}(V)} ≤ ‖uP‖_{W^{k+2,p}(V × B₁)}`
(`paddingDistributionTensor_noDrift_sobolevXENorm_le`), while `‖fP‖_{W^{k,p}(W × B₂)} ≤ |B₂|^{1/p} ‖f‖_{W^{k,p}(W)}`
and `‖uP‖_{L^p(W × B₂)} ≤ |B₂|^{1/p} ‖u‖_{L^p(W)}` (`sobolevXENorm_paddingNoDrift_pullback_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- BB Thm 11.1 (no drift, all `k`, `L^p`): the statement of
`RothschildStein.rs3_no_drift_sobolev`, assuming the upstream bundle `U`
(`NoDriftSobolevHypotheses`: the lifting theorem statement, left differentiation `LeftDifferentiation` (which gives local solvability) and the higher Sobolev estimate in dimension `≥ 3`). -/
theorem rs3_no_drift_sobolev_of_hypotheses (U : NoDriftSobolevHypotheses)
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
  have hpt : p ≠ ⊤ := hp_top.ne
  have hp1 : 1 ≤ p := hp.le
  -- fibers, cylinders, the padded system
  have hJ1pos := volume_fiberBall_pos (r := 1) one_pos
  have hJ2pos := volume_fiberBall_pos (r := 2) two_pos
  have hJ3pos := volume_fiberBall_pos (r := 3) (by norm_num)
  have hJ1top := volume_fiberBall_lt_top 1
  have hJ2top := volume_fiberBall_lt_top 2
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
  have hWΩ' : (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hWΩ
  have hVΩ' : (V : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans (hVW.trans hWΩ')
  have hWΩle : W ≤ Ω := hWΩ'
  have hVΩle : V ≤ Ω := hVΩ'
  let XP : Fin (q + 3) → (Fin (n + 3) → ℝ) → (Fin (n + 3) → ℝ) :=
    paddingNoDriftVectorFields (d := 3) X
  have hXP : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (XP i) (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) :=
    contDiffOn_paddingNoDriftVectorFields_projection (Ω : Set (Fin n → ℝ))
      (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) (padding_cylinder_subset_base Ω J₃) X hX
  have hspanP := bracketSpansOn_paddingNoDrift (d := 3) Ω J₃ X hX hspan
  obtain ⟨CP, hCP, hcore⟩ := rs3_no_drift_sobolev_core U (n := n + 3) (q := q + 3) (by omega)
    (by omega) (cylinder Ω J₃) (cylinder V J₁) (cylinder W J₂)
    (isCompact_closure_cylinder hV hJ1c) (closure_cylinder_subset hVW hJ12)
    (isCompact_closure_cylinder hW hJ2c) (closure_cylinder_subset hWΩ hJ23)
    XP hXP hspanP k p hp hp_top
  -- the constants
  set a : ℝ := (volume (J₁ : Set (Fin 3 → ℝ))).toReal ^ (1 / p.toReal) with ha
  set b : ℝ := (volume (J₂ : Set (Fin 3 → ℝ))).toReal ^ (1 / p.toReal) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos (ENNReal.toReal_pos hJ1pos.ne' hJ1top.ne) _
  have hb0 : 0 < b := Real.rpow_pos_of_pos (ENNReal.toReal_pos hJ2pos.ne' hJ2top.ne) _
  refine ⟨CP * b / a, by positivity, fun T f hf hT => ?_⟩
  have hfloc : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume := hT.1
  have hw : paddingNoDriftWeights (d := 3) (noDriftWeight : Fin q → ℕ+) =
      (noDriftWeight : Fin (q + 3) → ℕ+) := paddingNoDriftWeights_noDriftWeight
  -- the padded data
  have hfP : memSobolevX noDriftWeight XP (cylinder Ω J₃) k p (fun ξ => f (basePoint ξ)) := by
    have := memSobolevX_paddingNoDrift_lift Ω J₃ hJ3pos hJ3top noDriftWeight X hX p hp1 hpt f hf
    rwa [hw] at this
  have hfPloc : LocallyIntegrableOn (fun ξ => f (basePoint ξ))
      (cylinder Ω J₃ : Set (Fin (n + 3) → ℝ)) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hfP.1.locallyIntegrable hp1)
  have hTP : hasDistributionEquation (cylinder Ω J₃) XP hXP
      (paddingDistributionTensorOneCLM Ω (cylinder Ω J₃) (padding_cylinder_subset_base Ω J₃) T)
      (fun ξ => f (basePoint ξ)) := by
    refine ⟨hfPloc, fun φ => ?_⟩
    have h1 := paddingDistributionTensor_noDrift_equation Ω (cylinder Ω J₃)
      (padding_cylinder_subset_base Ω J₃) X hX T (Distribution.ofFun Ω f volume (⊤ : ℕ∞)) hT.2 φ
    rw [paddingDistributionTensorOneCLM_ofFun Ω J₃ hJ3top.ne f hfloc] at h1
    exact h1
  obtain ⟨uP, huPloc, hTuP, huPLoc, hest⟩ := hcore _ _ hfP hTP
  -- the descended function
  set η₁ := fiberBump 1 (by norm_num) with hη₁
  set η₂ := fiberBump 2 (by norm_num) with hη₂
  set η₃ := fiberBump 3 (by norm_num) with hη₃
  set u : (Fin n → ℝ) → ℝ := P2.fiberAvg uP η₃ with hu
  obtain ⟨hrep, hae⟩ := paddingDistributionTensor_descent Ω J₃ hJ3top.ne η₃ (fiberBump_integral 3 _)
    T uP huPloc hTuP
  have hrepV : ∀ {A : Opens (Fin n → ℝ)} {r : ℝ} (hA : A ≤ Ω) (hr : r ≤ 3) (hr0 : 1 / 2 < r),
      paddingDistributionTensorOneCLM A (cylinder A (fiberBall r))
          (padding_cylinder_subset_base A (fiberBall r))
          (RothschildStein.S.distributionRestrictionCLM Ω A T) =
        Distribution.ofFun (cylinder A (fiberBall r)) uP volume (⊤ : ℕ∞) := by
    intro A r hA hr hr0
    exact paddingTensor_restrict_ofFun Ω A hA J₃ (fiberBall r) (fiberBall_mono hr) T huPloc hTuP
  refine ⟨u, hrep.1, hrep.2, fun V' hV'c hV'Ω => ?_, ?_⟩
  · -- `u ∈ W^{k+2,p}(V')` through the padded cylinder `V' × B₂`
    have hV'Ω' : (V' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hV'Ω
    have hV'le : V' ≤ Ω := hV'Ω'
    have hSob : memSobolevX noDriftWeight XP (cylinder V' J₂) (k + 2) p uP :=
      huPLoc _ (isCompact_closure_cylinder hV'c hJ2c) (closure_cylinder_subset hV'Ω hJ23)
    rw [← hw] at hSob
    exact (paddingDistributionTensor_noDrift_sobolev_descent V' J₂ hJ2pos hJ2top
      η₂ (fiberBump_integral 2 _) noDriftWeight X (fun i => (hX i).mono hV'Ω') hp1 hpt
      (RothschildStein.S.distributionRestrictionCLM Ω V' T) uP
      (huPloc.mono_set (cylinder_subset hV'le (fiberBall_mono (by norm_num))))
      (hrepV hV'le (by norm_num) (by norm_num)) hSob).2
  · -- the estimate on `V ⋐ W`
    have hdesc := paddingDistributionTensor_noDrift_sobolevXENorm_le (k := k + 2) V J₁ hJ1top η₁
      (fiberBump_integral 1 _) noDriftWeight X (fun i => (hX i).mono hVΩ') hp1 hpt
      (RothschildStein.S.distributionRestrictionCLM Ω V T) uP
      (huPloc.mono_set (cylinder_subset hVΩle (fiberBall_mono (by norm_num))))
      (hrepV hVΩle (by norm_num) (by norm_num))
    rw [hw, ← ha] at hdesc
    -- the norms on `W × B₂`
    have hWle : cylinder W J₂ ≤ cylinder Ω J₃ := cylinder_mono hWΩle (fiberBall_mono (by norm_num))
    have hfPW := sobolevXENorm_paddingNoDrift_pullback_le (k := k) W J₂ hJ2pos hJ2top noDriftWeight
      X (fun i => (hX i).mono hWΩ') p hp1 hpt f (hfloc.mono_set hWΩ')
    rw [hw, ← hb] at hfPW
    have huloc : LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume := hrep.1
    have huPW := sobolevXENorm_paddingNoDrift_pullback_le (k := 0) W J₂ hJ2pos hJ2top noDriftWeight
      X (fun i => (hX i).mono hWΩ') p hp1 hpt u (huloc.mono_set hWΩ')
    rw [hw, ← hb, sobolevXENorm_zero_eq_eLpNorm _ _ _ hp1,
      sobolevXENorm_zero_eq_eLpNorm _ _ _ hp1] at huPW
    have hae' : uP =ᵐ[volume.restrict (cylinder W J₂ : Set (Fin (n + 3) → ℝ))]
        fun ξ => u (basePoint ξ) :=
      ae_restrict_of_ae_restrict_of_subset hWle hae
    have huPL : eLpNorm uP p (volume.restrict (cylinder W J₂ : Set (Fin (n + 3) → ℝ))) ≤
        ENNReal.ofReal b * eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ))) := by
      rw [eLpNorm_congr_ae hae']
      exact huPW
    refine descent_arith ha0 hb0 hCP ?_
    calc ENNReal.ofReal a * sobolevXENorm noDriftWeight X V (k + 2) p u
        ≤ sobolevXENorm noDriftWeight XP (cylinder V J₁) (k + 2) p uP := hdesc
      _ ≤ ENNReal.ofReal CP * (sobolevXENorm noDriftWeight XP (cylinder W J₂) k p
            (fun ξ => f (basePoint ξ)) + eLpNorm uP p (volume.restrict
              (cylinder W J₂ : Set (Fin (n + 3) → ℝ)))) := hest
      _ ≤ ENNReal.ofReal CP * (ENNReal.ofReal b * sobolevXENorm noDriftWeight X W k p f +
            ENNReal.ofReal b * eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) := by
          gcongr

end RothschildStein.P2

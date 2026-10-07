-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CompactAmbientBallFacts
public import RothschildStein.L1.FixedLiftBallProjection
public import RothschildStein.L1.CoordinateApproximationData
public import RothschildStein.L1.ProjectedFreePatch

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1.CoordinateApproximationData

/-- Every coordinate data set has
compact-uniform ambient containment, openness, measurability, positive
finite volumes of both balls and the projection inequality.
The fiber inequalities and power law are separate (BB pp. 516–522). -/
theorem compact_ball_facts {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData k s (n+m) w} (A : CoordinateApproximationData L M)
    (hΩ : IsOpen Ω) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ A.U) :
    ∃ rstar : ℝ, 0 < rstar ∧ ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
      let Ul := rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η r
      let Vb := rsBall Ω w X (basePoint η) r
      Ul ⊆ A.U ∧ IsOpen Ul ∧ IsOpen Vb ∧
      MeasurableSet Ul ∧ MeasurableSet Vb ∧
      volume Ul ≠ ⊤ ∧ volume Vb ≠ ⊤ ∧
      0 < (volume Ul).toReal ∧ 0 < (volume Vb).toReal ∧
      (∀ ξ ∈ Ul, controlDistance Ω w X (basePoint η) (basePoint ξ) ≤
        controlDistance (basePoint ⁻¹' Ω) w (triangularLift X L.P) η ξ) := by
  have hAU : A.U ⊆ (L.U : Set _) := fun _ hξ => A.closure_subset_lift (subset_closure hξ)
  have hAO : A.U ⊆ basePoint ⁻¹' Ω := hAU.trans L.subset_domain
  have hstep : bracketStepOn A.U w (triangularLift X L.P) s :=
    fun ξ hξ => (L.free_spanning ξ (hAU hξ)).2
  obtain ⟨rstar,hrstar,hfacts⟩ := exists_compact_ambient_ball_facts A.isOpen_U
    A.isCompact_closure_U hK hKU w hs hw (triangularLift X L.P)
    (fun i => (L.smooth i).mono hAO) hstep
  have hBase : Continuous (basePoint (n := n) (m := m)) := (P1.paddingBaseCLM n m).continuous
  have hBC := A.isCompact_closure_U.image hBase
  refine ⟨rstar,hrstar,?_⟩
  intro η hη r hr hrr Ul Vb
  obtain ⟨hsub,ho,hm,hfin,hpos⟩ := hfacts (basePoint ⁻¹' Ω) hAO η hη r hr hrr.le
  have hproj : basePoint '' Ul = Vb := L.rsBall_projection_eq hΩ η r
  have hVo : IsOpen Vb := by
    rw [← hproj]
    exact isOpen_basePoint_image ho
  have hVsub : Vb ⊆ basePoint '' closure A.U := by
    rw [← hproj]
    exact Set.image_mono (hsub.trans subset_closure)
  have hVfin : volume Vb ≠ ⊤ :=
    ne_top_of_le_ne_top hBC.measure_lt_top.ne (measure_mono hVsub)
  have hself : basePoint η ∈ Vb := by
    refine ⟨hAO (hKU hη),?_⟩
    rw [G1.controlDistance_self (Ω := Ω) w X (x := basePoint η) (hAO (hKU hη))]
    exact ENNReal.ofReal_pos.mpr hr
  exact ⟨hsub,ho,hVo,hm,hVo.measurableSet,hfin,hVfin,hpos,
    ENNReal.toReal_pos (hVo.measure_pos volume ⟨basePoint η,hself⟩).ne' hVfin,
    fun ξ _ => L.controlDistance_projection_le hΩ η ξ⟩

end RothschildStein.L1.CoordinateApproximationData

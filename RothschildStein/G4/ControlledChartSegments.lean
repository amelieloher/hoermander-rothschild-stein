-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ContinuousCramerAlong
public import RothschildStein.G4.WeightedSmallControlBounds
public import RothschildStein.G4.AuxiliaryControl

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace RothschildStein.G4

/-- Actual chart images of small coordinate segments are controlled
curves in the original ambient domain. The controls are actual Cramer
coordinates, with their measurability and ODE proved (BB p. 457). -/
theorem chart_segment_isControlledCurve {m n s : ℕ}
    (w : Fin m → ℕ+) (B : Fin n → Fin m) (hB : Function.Injective B)
    (hw : ∀ i, (w (B i) : ℕ) ≤ s)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {Ω : Set (Fin n → ℝ)} (hZ : ∀ J, ContinuousOn (Z J) Ω)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) {β r κ d : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hr : 0 < r) (hκ : 0 ≤ κ)
    (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (hd : 0 < d) (hd1 : d ≤ 1) (hmargin : 3 * β ≤ d ^ s)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (weightedBox (w ∘ B) (β * r)))
    (hmap : MapsTo F (weightedBox (w ∘ B) (β * r)) Ω)
    (hdet : ∀ u ∈ weightedBox (w ∘ B) (β * r), frameDet Z B (F u) ≠ 0)
    (herror : ∀ u ∈ weightedBox (w ∘ B) (β * r), ∀ j i,
      |frameCoefficient Z B (fun z => fderiv ℝ F u (Pi.single i 1) - Z (B i) z)
        j (F u)| ≤ κ * r ^ (((w (B j) : ℕ) : ℤ) - ((w (B i) : ℕ) : ℤ)))
    {u v : Fin n → ℝ} (hu : u ∈ weightedBox (w ∘ B) (β * r))
    (hv : v ∈ weightedBox (w ∘ B) (β * r)) :
    isControlledCurve Ω w Z (d * r) (fun t => F (u + t • (v - u))) := by
  let Q := weightedBox (w ∘ B) (β * r)
  let h : ℝ → (Fin n → ℝ) := fun t => u + t • (v - u)
  let γ := F ∘ h
  have hQ : IsOpen Q := isOpen_weightedBox _ _
  have hh : MapsTo h (Icc (0 : ℝ) 1) Q := by
    intro t ht
    have hmem := (convex_weightedBox (w ∘ B) (β * r)) hu hv
      (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (by ring : 1 - t + t = 1)
    convert hmem using 1
    ext i
    simp only [h, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) h :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγsmooth : ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc (0 : ℝ) 1) :=
    hF.comp hsmooth.contDiffOn hh
  have hhder : ∀ t, HasDerivAt h (v - u) t := by
    intro t
    convert (hasDerivAt_const t u).add ((hasDerivAt_id t).smul_const (v - u)) using 1
    · funext q; rfl
    · simp only [zero_add, one_smul]
  let E : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t j i => frameCoefficient Z B
    (fun z => fderiv ℝ F (h t) (Pi.single i 1) - Z (B i) z) j (γ t)
  let c : Fin n → ℝ → ℝ := fun j t => (v - u) j + (E t).mulVec (v - u) j
  have hγcont : Continuous (fun t : Icc (0 : ℝ) 1 => γ t.val) := hγsmooth.continuousOn.domRestrict
  have hTcont : Continuous (fun t : Icc (0 : ℝ) 1 => fderiv ℝ F (h t.val)) :=
    (hF.continuousOn_fderiv_of_isOpen hQ (by simp)).comp_continuous
      (hsmooth.continuous.comp continuous_subtype_val) (fun t => hh t.property)
  have hcolumns : ∀ j, Continuous (fun t : Icc (0 : ℝ) 1 => Z (B j) (γ t.val)) :=
    fun j => (hZ (B j)).comp_continuous hγcont (fun t => hmap (hh t.property))
  have hEcont : ∀ j i, Continuous (fun t : Icc (0 : ℝ) 1 => E t.val j i) := by
    intro j i
    exact continuous_frameCoefficient_along Z B _ _ hcolumns
      ((hTcont.clm_apply continuous_const).sub (hcolumns i))
      (fun t => hdet _ (hh t.property)) j
  have hccont : ∀ j, ContinuousOn (c j) (Icc (0 : ℝ) 1) := by
    intro j
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun t : Icc (0 : ℝ) 1 =>
      (v - u) j + ∑ i, E t.val j i * (v - u) i)
    exact continuous_const.add (continuous_finsetSum _ (fun i _ =>
      (hEcont j i).mul continuous_const))
  have hcost : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, |c j t| ≤ (d * r) ^ (w (B j) : ℕ) := by
    intro t ht
    exact weighted_control_cost_from_linear_bound (w ∘ B) hw hd.le hd1 hr.le hmargin
      (contraction_tangent_control_bound (w ∘ B) (E t) hβ.le hβ1 hr hκ hsmall
        (herror _ (hh ht)) hu hv)
  have hode : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt γ (∑ j, c j t • Z (B j) (γ t)) t := by
    intro t ht
    have hdF := ((hF.contDiffAt (hQ.mem_nhds (hh ht))).differentiableAt
      (by simp)).hasFDerivAt
    have hrep := actual_chart_tangent_representation Z B (fderiv ℝ F (h t))
      (hdet _ (hh ht)) (v - u)
    change fderiv ℝ F (h t) (v - u) = ∑ j, c j t • Z (B j) (γ t) at hrep
    rw [← hrep]
    exact hdF.comp_hasDerivAt t (hhder t)
  apply isControlledCurve_extend B hB (fun _ => rfl) (fun _ => rfl)
  refine ⟨mul_pos hd hr, ?_, fun t ht => hmap (hh ht), c,
    fun j => (hccont j).aemeasurable measurableSet_Icc, ?_⟩
  · have hγ1 : ContDiffOn ℝ 1 γ (uIcc (0 : ℝ) 1) := by
      rw [uIcc_of_le zero_le_one]
      exact hγsmooth.of_le (by simp)
    exact hγ1.absolutelyContinuousOnInterval
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨hcost t ht, hode t ht⟩

end RothschildStein.G4

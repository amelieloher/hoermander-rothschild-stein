-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SmoothHeatRepresentatives
public import HeatKernel.Kernel.CoordinateRepresentatives
public import HeatKernel.Kernel.CoordinateDerivatives
public import HeatKernel.Kernel.ClassicalHeatEquation

/-! # Smooth heat representatives from almost-everywhere time sections

Local hypoellipticity smooths a locally integrable weak representative.
Its almost-everywhere time sections and L² continuity identify every section.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HeatKernel

open RothschildStein

/-- A weak heat representative of an L²-continuous curve has unique smooth classical sections. -/
theorem exists_smooth_L2_heat_representative_of_ae_sections {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT : ContinuousOn T (Set.Ioi 0)) (u : (Fin (1 + n) → ℝ) → ℝ)
    (hu : LocallyIntegrableOn u {x | 0 < x 0} volume)
    (hslice : ∀ᵐ t ∂volume, 0 < t →
      (fun x => u ((timeSpaceCoordinates n).symm (t, x))) =ᵐ[volume] T t)
    (hweak : ∀ φ : (Fin (1 + n) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {x | 0 < x 0} →
      (∫ x in {x | 0 < x 0}, u x *
        (fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
          ∑ i : Fin q, fderiv ℝ
            (fun y => fderiv ℝ φ y (liftRightField 1 (G.horizontalFields hq i) y)) x
            (liftRightField 1 (G.horizontalFields hq i) x))) = 0) :
    ∃ v : (Fin (1 + n) → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v {x | 0 < x 0} ∧
      u =ᵐ[volume.restrict {x | 0 < x 0}] v ∧
      (∀ t : ℝ, 0 < t →
        ∃ h : MemLp (fun x => v ((timeSpaceCoordinates n).symm (t, x))) 2 volume,
          h.toLp (fun x => v ((timeSpaceCoordinates n).symm (t, x))) = T t) ∧
      (∀ x : Fin (1 + n) → ℝ, 0 < x 0 →
        fderiv ℝ v x (leftCoordinateInclusion 1 n (fun _ => 1)) =
          ∑ i : Fin q, fderiv ℝ
            (fun y => fderiv ℝ v y (liftRightField 1 (G.horizontalFields hq i) y)) x
            (liftRightField 1 (G.horizontalFields hq i) x)) ∧
      (∀ w : (Fin (1 + n) → ℝ) → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) w {x | 0 < x 0} →
        u =ᵐ[volume.restrict {x | 0 < x 0}] w → Set.EqOn v w {x | 0 < x 0}) := by
  obtain ⟨v, hv, huv, hunique⟩ :=
    exists_unique_smooth_heat_representative_of_integral_identity G hq hspan u hu hweak
  have hvweak : ∀ φ : (Fin (1 + n) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {x | 0 < x 0} →
      (∫ x in {x | 0 < x 0}, v x *
        (fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
          ∑ i : Fin q, fderiv ℝ
            (fun y => fderiv ℝ φ y (liftRightField 1 (G.horizontalFields hq i) y)) x
            (liftRightField 1 (G.horizontalFields hq i) x))) = 0 := by
    intro φ hφ hcompact hsupp
    calc
      _ = ∫ x in {x | 0 < x 0}, u x *
          (fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
            ∑ i : Fin q, fderiv ℝ
              (fun y => fderiv ℝ φ y (liftRightField 1 (G.horizontalFields hq i) y)) x
              (liftRightField 1 (G.horizontalFields hq i) x)) := by
        apply integral_congr_ae
        filter_upwards [huv] with x hx
        rw [hx]
      _ = 0 := hweak φ hφ hcompact hsupp
  refine ⟨v, hv, huv, ?_, ?_, hunique⟩
  · intro t ht
    let e := timeSpaceCoordinates n
    have hmeasure := MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      (measurePreserving_timeSpaceCoordinates_positive n)
    have hproduct : (fun p => u (e.symm p)) =ᵐ[(volume.restrict (Set.Ioi 0)).prod volume]
        (fun p => v (e.symm p)) := hmeasure.quasiMeasurePreserving.ae_eq_comp huv
    have hsections : ∀ᵐ s ∂volume, 0 < s →
        (fun x => u (e.symm (s, x))) =ᵐ[volume] (fun x => v (e.symm (s, x))) :=
      (ae_restrict_iff' measurableSet_Ioi).mp (Measure.ae_ae_of_ae_prod hproduct)
    have hvsections : ∀ᵐ s ∂volume.restrict (Set.Ioi 0),
        (fun x => v (e.symm (s, x))) =ᵐ[volume] T s := by
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      filter_upwards [hsections, hslice] with s hs hsu hpos
      exact (hs hpos).symm.trans (hsu hpos)
    have hcont : ContinuousOn (fun p => v (e.symm p)) (Set.Ioi 0 ×ˢ Set.univ) := by
      apply hv.continuousOn.comp e.symm.continuous.continuousOn
      intro p hp
      change 0 < (timeSpaceCoordinates n).symm p 0
      rw [timeSpaceCoordinates_symm_time]
      exact hp.1
    have heq := ae_eq_sections_of_continuous_L2 isOpen_Ioi
      (fun p => v (e.symm p)) T hcont hT hvsections t ht
    have hmem : MemLp (fun x => v (e.symm (t, x))) 2 volume :=
      (Lp.memLp (T t)).ae_eq heq.symm
    refine ⟨hmem, ?_⟩
    apply Lp.ext
    exact hmem.coeFn_toLp.trans heq
  · intro x hx
    exact fderiv_time_eq_horizontal_squares_of_integral_identity G hq v hv hvweak hx

end HeatKernel

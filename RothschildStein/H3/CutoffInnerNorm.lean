-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- On the open plateau of a cutoff, each local weak word norm
is bounded by its global product norm (BB Lemma 8.42, p. 371). -/
theorem cutoff_plateau_weakNorm_le {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (U : Opens (Fin n → ℝ)) (I : List (Fin m)) (p : ℝ≥0∞)
    (u φ g : (Fin n → ℝ) → ℝ)
    (hφ : EqOn φ 1 (U : Set (Fin n → ℝ)))
    (hg : hasWeakWordDeriv X ⊤ I (fun x => u x * φ x) g) :
    weakWordENorm X U I p u ≤
      weakWordENorm X ⊤ I p (fun x => u x * φ x) := by
  have hr := S.hasWeakWordDeriv_restrict X ⊤ U (subset_univ _) hg
  have he : (fun x => u x * φ x) =ᵐ[volume.restrict (U : Set (Fin n → ℝ))] u := by
    rw [Filter.EventuallyEq, ae_restrict_iff' U.isOpen.measurableSet]
    filter_upwards [] with x
    intro hx
    simp [hφ hx]
  have hu := S.hasWeakWordDeriv_congr_ae X U hr he Filter.EventuallyEq.rfl
  rw [S.weakWordENorm_eq X U I p u g hu,
    S.weakWordENorm_eq X ⊤ I p _ g hg]
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    eLpNorm_mono_measure g (Measure.restrict_le_self (μ := volume) (s := (U : Set (Fin n → ℝ))))

end RothschildStein.H3

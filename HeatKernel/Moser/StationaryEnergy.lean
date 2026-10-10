-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import HeatKernel.Moser.LocalHorizontalDerivatives

/-!
# Local energy bounds for stationary functions

A local horizontal Sobolev function, viewed as constant in time, has bounded
local spatial L² norm and square-integrable horizontal derivatives on compact
space-time sets. See Sturm 1996, Proposition 3.2.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace
open RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- A local horizontal Sobolev function has bounded spatial L² norm when held constant in time. -/
theorem essSup_stationary_eLpNorm_lt_top {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight X Ω 1 2 u)
    (J : Set ℝ) {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hsub : K ⊆ Ω) :
    essSup (fun _t : ℝ => eLpNorm u 2 (volume.restrict K)) (volume.restrict J) < ⊤ := by
  have hLp := memLp_two_on_compact_of_memSobolevXLoc hu hK hsub
  exact (essSup_le_of_ae_le _ (ae_of_all _ (fun _ => le_rfl))).trans_lt hLp.eLpNorm_lt_top

/-- A spatial L² function gives a space-time L² function on every compact time set. -/
theorem memLp_two_stationary_on_compact_time {n : ℕ}
    {g : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}
    (hg : MemLp g 2 (volume.restrict K)) {J : Set ℝ} (hJ : IsCompact J) :
    MemLp (fun z : ℝ × (Fin n → ℝ) => g z.2) 2
      (volume.restrict (J ×ˢ K)) := by
  let : IsFiniteMeasure (volume.restrict J) := ⟨by simpa using hJ.measure_lt_top⟩
  have h := hg.comp_snd (volume.restrict J)
  rw [Measure.prod_restrict] at h
  exact h

/-- Horizontal weak derivatives of a stationary local Sobolev function have local space-time L² bounds. -/
theorem memLp_two_stationary_horizontal_on_compact {m n : ℕ}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {u g : (Fin n → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight X Ω 1 2 u)
    {J : Set ℝ} (hJ : IsCompact J) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hsub : K ⊆ Ω) (i : Fin m)
    (hg : hasWeakWordDeriv X Ω [i] u g) :
    MemLp (fun z : ℝ × (Fin n → ℝ) => g z.2) 2
      (volume.restrict (J ×ˢ K)) := by
  exact memLp_two_stationary_on_compact_time
    (memLp_two_horizontal_on_compact_of_memSobolevXLoc hu hK hsub i hg) hJ

end HeatKernel

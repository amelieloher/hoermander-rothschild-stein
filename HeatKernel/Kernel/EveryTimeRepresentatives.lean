-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Identification of continuous spacetime representatives at every time

Compact spatial tests give continuous pairings of a continuous spacetime function.
Continuity of both pairings upgrades almost-everywhere time agreement to every time;
uniqueness against smooth tests then identifies each spatial section almost everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Compactly supported continuous spatial tests give continuous time pairings. -/
theorem continuousOn_integral_compact_test {n : ℕ} {I : Set ℝ}
    (u : ℝ × (Fin n → ℝ) → ℝ) (hu : ContinuousOn u (I ×ˢ Set.univ))
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hcompact : HasCompactSupport φ) :
    ContinuousOn (fun t => ∫ x, φ x * u (t, x)) I := by
  apply continuousOn_integral_of_compact_support hcompact
  · exact (hφ.comp continuous_snd).continuousOn.mul hu
  · intro t x _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Continuous test pairings determine every section from almost-everywhere time agreement. -/
theorem ae_eq_sections_of_continuous_test_pairings {n : ℕ} {I : Set ℝ}
    (hI : IsOpen I) (u : ℝ × (Fin n → ℝ) → ℝ)
    (U : ℝ → (Fin n → ℝ) → ℝ) (hu : ContinuousOn u (I ×ˢ Set.univ))
    (hU : ∀ t ∈ I, LocallyIntegrable (U t) volume)
    (hpair : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → ContinuousOn (fun t => ∫ x, φ x * U t x) I)
    (hae : ∀ᵐ t ∂volume.restrict I, (fun x => u (t, x)) =ᵐ[volume] U t) :
    ∀ t ∈ I, (fun x => u (t, x)) =ᵐ[volume] U t := by
  intro t ht
  have huc : Continuous (fun x => u (t, x)) := by
    apply continuousOn_univ.mp
    exact hu.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨ht, Set.mem_univ x⟩)
  apply ae_eq_of_integral_contDiff_smul_eq huc.locallyIntegrable (hU t ht)
  intro φ hφ hcompact
  have heq : (fun t => ∫ x, φ x * u (t, x)) =ᵐ[volume.restrict I]
      (fun t => ∫ x, φ x * U t x) := by
    filter_upwards [hae] with s hs
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    rw [hx]
  have heqOn := Measure.eqOn_open_of_ae_eq heq hI
    (continuousOn_integral_compact_test u hu φ hφ.continuous hcompact)
    (hpair φ hφ hcompact)
  simpa only [smul_eq_mul] using heqOn ht

/-- Strong continuity in L² gives continuous pairings with each square-integrable test. -/
theorem continuousOn_integral_mul_L2 {n : ℕ} {I : Set ℝ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (hT : ContinuousOn T I)
    (φ : (Fin n → ℝ) → ℝ) (hφ : MemLp φ 2 volume) :
    ContinuousOn (fun t => ∫ x, φ x * T t x) I := by
  have hcont : ContinuousOn (fun t => inner ℝ (hφ.toLp φ) (T t)) I :=
    continuousOn_const.inner hT
  have heq : (fun t => inner ℝ (hφ.toLp φ) (T t)) = fun t => ∫ x, φ x * T t x := by
    funext t
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  rw [heq] at hcont
  exact hcont

/-- A continuous spacetime version of an L²-continuous curve represents every time section. -/
theorem ae_eq_sections_of_continuous_L2 {n : ℕ} {I : Set ℝ}
    (hI : IsOpen I) (u : ℝ × (Fin n → ℝ) → ℝ)
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hu : ContinuousOn u (I ×ˢ Set.univ)) (hT : ContinuousOn T I)
    (hae : ∀ᵐ t ∂volume.restrict I, (fun x => u (t, x)) =ᵐ[volume] T t) :
    ∀ t ∈ I, (fun x => u (t, x)) =ᵐ[volume] T t := by
  apply ae_eq_sections_of_continuous_test_pairings hI u (fun t x => T t x) hu
  · intro t _
    exact (Lp.memLp (T t)).locallyIntegrable (by norm_num)
  · intro φ hφ hcompact
    exact continuousOn_integral_mul_L2 T hT φ (hφ.continuous.memLp_of_hasCompactSupport hcompact)
  · exact hae

end HeatKernel

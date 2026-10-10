-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.StationaryElliptic
public import HeatKernel.Moser.StationaryExtrema

/-! # Spatial Harnack estimates from finite parabolic cylinders

The finite time intervals in the parabolic comparison have positive measure.
Stationary extension therefore gives exactly the spatial essential-extremum estimate.
-/

@[expose] public section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Lebesgue measure restricted to a nonempty open interval is nonzero. -/
theorem volume_restrict_Ioo_ne_zero {a b : ℝ} (hab : a < b) :
    (volume : Measure ℝ).restrict (Ioo a b) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero]
  exact ne_of_gt (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))

/-- A parabolic Harnack estimate on the standard earlier and later time intervals implies
an elliptic Harnack estimate on the common spatial comparison set. -/
theorem elliptic_harnack_of_cylinder_harnack_estimate {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (Bouter Binner : Set (Fin N → ℝ)) (r s lam Λ H : ℝ) (hr : 0 < r) (hlam : 0 ≤ lam)
    (ha : ∀ i j, Measurable (fun x => a x i j))
    (hb : ∀ᵐ x ∂volume, (∀ i j, a x i j = a x j i) ∧
      ∀ ξ : Fin q → ℝ,
        lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a x i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2)
    (harnack : ∀ w : ℝ → (Fin N → ℝ) → ℝ,
      IsLocalWeakSolution G hq hqpos hw hspan (fun _ x => a x)
        ⟨Ioo (s - 4 * r ^ 2) s, isOpen_Ioo⟩ ⟨interior Bouter, isOpen_interior⟩ w →
      (∀ᵐ z ∂volume.restrict (Ioo (s - 4 * r ^ 2) s ×ˢ Bouter), 0 ≤ w z.1 z.2) →
      essSup (fun z => ENNReal.ofReal (w z.1 z.2))
        (volume.restrict (Ioo (s - 3 * r ^ 2) (s - 2 * r ^ 2) ×ˢ Binner)) ≤
      ENNReal.ofReal H * essInf (fun z => ENNReal.ofReal (w z.1 z.2))
        (volume.restrict (Ioo (s - r ^ 2) s ×ˢ Binner)))
    {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevXLoc noDriftWeight (G.horizontalFields hq)
      ⟨interior Bouter, isOpen_interior⟩ 1 2 u)
    (hell : ∃ g : Fin q → (Fin N → ℝ) → ℝ,
      (∀ i, hasWeakWordDeriv (G.horizontalFields hq)
        ⟨interior Bouter, isOpen_interior⟩ [i] u (g i)) ∧
      ∀ ψ : TestFunction ⟨interior Bouter, isOpen_interior⟩ ℝ (⊤ : ℕ∞),
        (∫ x in interior Bouter,
          ∑ i, ∑ j, a x i j * g j x * fieldDerivative (G.horizontalFields hq i) ψ x) = 0)
    (hupos : ∀ᵐ x ∂volume.restrict Bouter, 0 ≤ u x) :
    essSup (fun x => ENNReal.ofReal (u x)) (volume.restrict Binner) ≤
      ENNReal.ofReal H * essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict Binner) := by
  have hweak := isLocalWeakSolution_stationary_of_ellipticity G hq hqpos hw hspan a
    ⟨Ioo (s - 4 * r ^ 2) s, isOpen_Ioo⟩ ⟨interior Bouter, isOpen_interior⟩
    lam Λ hlam ha hb hu hell
  have hp : ∀ᵐ z ∂volume.restrict (Ioo (s - 4 * r ^ 2) s ×ˢ Bouter), 0 ≤ u z.2 := by
    have hp := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Ioo (s - 4 * r ^ 2) s)) (ν := volume.restrict Bouter)).ae hupos
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hp
  have he := harnack (fun _ x => u x) hweak hp
  have hminus : (volume : Measure ℝ).restrict (Ioo (s - 3 * r ^ 2) (s - 2 * r ^ 2)) ≠ 0 :=
    volume_restrict_Ioo_ne_zero (by nlinarith [sq_pos_of_pos hr])
  have hplus : (volume : Measure ℝ).restrict (Ioo (s - r ^ 2) s) ≠ 0 :=
    volume_restrict_Ioo_ne_zero (by nlinarith [sq_pos_of_pos hr])
  have hm : (volume : Measure (ℝ × (Fin N → ℝ))).restrict
      (Ioo (s - 3 * r ^ 2) (s - 2 * r ^ 2) ×ˢ Binner) =
      ((volume : Measure ℝ).restrict (Ioo (s - 3 * r ^ 2) (s - 2 * r ^ 2))).prod
        (volume.restrict Binner) := by rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hp' : (volume : Measure (ℝ × (Fin N → ℝ))).restrict (Ioo (s - r ^ 2) s ×ˢ Binner) =
      ((volume : Measure ℝ).restrict (Ioo (s - r ^ 2) s)).prod
        (volume.restrict Binner) := by rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [hm, hp', essSup_snd_eq_of_measure_ne_zero hminus (fun x => ENNReal.ofReal (u x)),
    essInf_snd_eq_of_measure_ne_zero hplus (fun x => ENNReal.ofReal (u x))] at he
  exact he

end HeatKernel

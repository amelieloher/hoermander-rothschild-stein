-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G2.Gauge
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}
/-- The unit sphere of every homogeneous gauge is nonempty and compact. -/
theorem homogeneousGauge_unitSphere {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) :
    IsCompact {x | ν x = 1} ∧ ({x | ν x = 1} : Set (Fin N → ℝ)).Nonempty := by
  have hc : IsCompact {x | ν x = 1} :=
    (isCompact_gauge_le hν 1).of_isClosed_subset
      (isClosed_eq hν.1 continuous_const) (fun _ hx => le_of_eq hx)
  let x : Fin N → ℝ := Pi.single ⟨0, G.dimension_pos⟩ 1
  have hx : x ≠ 0 := by
    intro h
    have he := congrFun h ⟨0, G.dimension_pos⟩
    simp [x] at he
  exact ⟨hc, ⟨G.dilate (ν x)⁻¹ x, gauge_normalize hν hx⟩⟩
/-- The sphere maximum gives the exact global homogeneous pointwise bound. -/
theorem homogeneous_function_sphere_bound {ν F : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (γ : ℝ)
    (hF : ContinuousOn F ({0}ᶜ))
    (hscale : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∃ w, ν w = 1 ∧ |F w| = M) ∧
      (∀ w, ν w = 1 → |F w| ≤ M) ∧
      ∀ x, x ≠ 0 → |F x| ≤ M * (ν x) ^ γ := by
  obtain ⟨hc, hn⟩ := homogeneousGauge_unitSphere hν
  have hs : {x | ν x = 1} ⊆ ({0}ᶜ : Set (Fin N → ℝ)) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hx0
    have hz := (hν.2.2.1 0).mpr rfl
    simp only [mem_ofPred_eq] at hx
    rw [hx0, hz] at hx
    norm_num at hx
  obtain ⟨w, hw, hmax⟩ := hc.exists_isMaxOn hn (hF.mono hs).abs
  refine ⟨|F w|, abs_nonneg _, ⟨w, hw, rfl⟩, fun z hz => hmax hz, ?_⟩
  intro x hx
  have hp := gauge_pos hν hx
  have he : F x = (ν x) ^ γ * F (G.dilate (ν x)⁻¹ x) := by
    conv_lhs => rw [← dilate_normalize hν hx]
    apply hscale (ν x) hp
    intro he0
    have hu := gauge_normalize hν hx
    rw [he0, (hν.2.2.1 0).mpr rfl] at hu
    norm_num at hu
  rw [he, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp γ)]
  calc
    _ ≤ (ν x) ^ γ * |F w| :=
      mul_le_mul_of_nonneg_left (hmax (gauge_normalize hν hx))
        (Real.rpow_nonneg hp.le γ)
    _ = _ := mul_comm _ _
/-- Nonpositive homogeneous degrees have a uniform exterior bound
at every positive gauge radius (BB Proposition 3.23, p. 107). -/
theorem homogeneous_function_exterior_bound {ν F : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {γ : ℝ} (hγ : γ ≤ 0)
    (hF : ContinuousOn F ({0}ᶜ))
    (hscale : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 0 < ρ → ∀ x, ρ ≤ ν x →
      |F x| ≤ M * ρ ^ γ := by
  obtain ⟨M, hM, _, _, hb⟩ := homogeneous_function_sphere_bound hν γ hF hscale
  refine ⟨M, hM, ?_⟩
  intro ρ hρ x hx
  have hx0 : x ≠ 0 := by
    intro he
    rw [he, (hν.2.2.1 0).mpr rfl] at hx
    exact (not_le_of_gt hρ) hx
  exact (hb x hx0).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hρ hx hγ) hM)
end RothschildStein.H3

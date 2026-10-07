-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplit
public import RothschildStein.G2.EuclideanComparison

/-!
# Uniform image radius of the endpoint chart

For a compact `K' ⊆ U` there is a radius `R > 0` such that, for every `ξ ∈ K'`, each `u` with
`‖u‖ < R` is of the form `Θ(η, ξ)` with `η ∈ U` (tube lemma applied to the open set `T` of
`isOpen_T`, then antisymmetry `Θ(ξ, η) = -Θ(η, ξ)`). The same holds for `ν u < R` when `ν` is a
homogeneous gauge. This is the "full annulus lies in the larger chart patch" input of the annular
cancellation (BB p. 574; also used for Data D3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The origin lies in the target of every endpoint chart `e ξ`, `ξ ∈ U`. -/
theorem zero_mem_e_target {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) : (0 : Fin (n + m) → ℝ) ∈ (C.e ξ).target := by
  obtain ⟨hsrc, hval, -, -, hΘ⟩ := C.chart ξ hξ
  have h := (C.e ξ).map_source (show ξ ∈ (C.e ξ).source by rw [hsrc]; exact hξ)
  rwa [hval ξ hξ, hΘ] at h

/-- The image of `η ↦ Θ(η, ξ)` on `U` contains the Euclidean `R`-ball once the tube
`{ξ} × ball 0 R` lies in the open set `T` of `isOpen_T`. The elementary form of the uniform
image radius. -/
theorem exists_mem_Θ_of_mem_target {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {u : Fin (n + m) → ℝ} (hu : -u ∈ (C.e ξ).target) : ∃ η ∈ C.U, C.Θ η ξ = u := by
  obtain ⟨hsrc, hval, -, -, -⟩ := C.chart ξ hξ
  obtain ⟨η, hη, hηu⟩ := (C.e ξ).image_source_eq_target ▸ hu
  rw [hsrc] at hη
  refine ⟨η, hη, ?_⟩
  have h1 := C.theta_antisymm η hη ξ hξ
  rw [hval η hη] at hηu
  rw [h1] at hηu
  exact neg_injective hηu

/-- Uniform target radius (Euclidean form): for compact `K' ⊆ U` there is `R > 0` such
that the Euclidean `R`-ball lies in the target of the chart `e ξ` for every `ξ ∈ K'` (tube lemma
for the open set `T` of the lifted-chart field `isOpen_T`). -/
theorem exists_ball_subset_e_target {K' : Set (Fin (n + m) → ℝ)} (hK : IsCompact K')
    (hKU : K' ⊆ C.U) :
    ∃ R : ℝ, 0 < R ∧ ∀ ξ ∈ K', ∀ u : Fin (n + m) → ℝ, ‖u‖ < R → u ∈ (C.e ξ).target := by
  have hS : IsCompact (K' ×ˢ ({0} : Set (Fin (n + m) → ℝ))) := hK.prod isCompact_singleton
  have hsub : K' ×ˢ ({0} : Set (Fin (n + m) → ℝ)) ⊆
      {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.1 ∈ C.U ∧ z.2 ∈ (C.e z.1).target} := by
    rintro ⟨ξ, u⟩ ⟨hξ, hu⟩
    have hu0 : u = 0 := hu
    subst hu0
    exact ⟨hKU hξ, C.zero_mem_e_target (hKU hξ)⟩
  obtain ⟨δ, hδ, hthick⟩ := hS.exists_thickening_subset_open C.isOpen_T hsub
  refine ⟨δ, hδ, fun ξ hξ u hu => ?_⟩
  have hmem : (ξ, u) ∈ thickening δ (K' ×ˢ ({0} : Set (Fin (n + m) → ℝ))) := by
    rw [mem_thickening_iff]
    refine ⟨(ξ, 0), ⟨hξ, rfl⟩, ?_⟩
    rw [Prod.dist_eq]
    simpa [dist_eq_norm] using hu
  exact (hthick hmem).2

/-- Uniform image radius (Euclidean form): for compact `K' ⊆ U` there is `R > 0` such
that for every `ξ ∈ K'` each `u` with `‖u‖ < R` equals `Θ(η, ξ)` for some `η ∈ U`
(BB p. 574; chart: lifted-chart fields `chart`, `isOpen_T`, `theta_antisymm`). -/
theorem exists_image_radius {K' : Set (Fin (n + m) → ℝ)} (hK : IsCompact K') (hKU : K' ⊆ C.U) :
    ∃ R : ℝ, 0 < R ∧ ∀ ξ ∈ K', ∀ u : Fin (n + m) → ℝ, ‖u‖ < R →
      ∃ η ∈ C.U, C.Θ η ξ = u := by
  obtain ⟨R, hR, htarget⟩ := C.exists_ball_subset_e_target hK hKU
  refine ⟨R, hR, fun ξ hξ u hu => ?_⟩
  exact C.exists_mem_Θ_of_mem_target (hKU hξ) (htarget ξ hξ (-u) (by simpa using hu))

/-- Uniform image radius for a homogeneous gauge `ν`: for compact `K' ⊆ U` there is
`R > 0` such that for every `ξ ∈ K'` each `u` with `ν u < R` equals `Θ(η, ξ)` for some `η ∈ U`
(the gauge sublevel lies in a Euclidean ball, `G2.gauge_sublevel_norm_comparison`). -/
theorem exists_gauge_image_radius {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    {K' : Set (Fin (n + m) → ℝ)} (hK : IsCompact K') (hKU : K' ⊆ C.U) :
    ∃ R : ℝ, 0 < R ∧ ∀ ξ ∈ K', ∀ u : Fin (n + m) → ℝ, ν u < R →
      ∃ η ∈ C.U, C.Θ η ξ = u := by
  obtain ⟨R₁, hR₁, hcover⟩ := C.exists_image_radius hK hKU
  obtain ⟨a, b, ha, hb, hcomp⟩ := G2.gauge_sublevel_norm_comparison hν 1
  refine ⟨min 1 (a * R₁), lt_min one_pos (mul_pos ha hR₁), fun ξ hξ u hu => ?_⟩
  apply hcover ξ hξ u
  have h1 : ν u < 1 := hu.trans_le (min_le_left _ _)
  have h2 : ν u < a * R₁ := hu.trans_le (min_le_right _ _)
  have h3 := (hcomp u h1.le).1
  by_contra hcon
  have hcon' : R₁ ≤ ‖u‖ := not_lt.mp hcon
  have : a * R₁ ≤ a * ‖u‖ := mul_le_mul_of_nonneg_left hcon' ha.le
  linarith

end LiftedChart
end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2CertificateTruncation
public import RothschildStein.P1.SingularSplitRadius

/-!
# Common radial support radius `R'`

Given the geometry `(Ω₀ ⋐ Ω₁ ⋐ Ω₂, κ)`, the truncation `(θ₁, τ)` and a common radius
`0 < r < κ`, a radius `R'` is admissible if `0 < R' ≤ θ₁ r / 4`, `R' < θ₁ τ / 2`, and `R'` lies
below the uniform chart-image radius and the positive-density threshold `1 + ω₋ ≥ 1/2` on the
compact closure of `Ω₂` (BB pp. 574–576). Admissible radii form
a down-closed set, so later smallness requirements may shrink `R'` further. All choices are
independent of the function acted on.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

namespace LiftedChart

variable (C : LiftedChart w s Ω hΩ X x₀ m)

/-- An admissible common radial support radius `R'`: `0 < R' ≤ θ₁ r / 4`, `R' < θ₁ τ / 2`, every `u` with `ν u < R'` is of the form
`Θ(η, x)` with `η ∈ U` for all `x` over `closure Ω₂` (uniform chart-image radius, so the whole
model shell lies in the image), and `1/2 ≤ 1 + ω±` there (positive-density threshold). -/
structure IsAdmissibleRadius (S : H2.LocDoubling C.Carrier) (T : H2.TruncDist S)
    (ν : (Fin (n + m) → ℝ) → ℝ) (τ r R' : ℝ) : Prop where
  pos : 0 < R'
  le_cover : R' ≤ T.θ₁ * r / 4
  lt_trunc : R' < T.θ₁ * τ / 2
  chart_image : ∀ x ∈ closure S.Ω₂, ∀ u : Fin (n + m) → ℝ, ν u < R' →
    ∃ η ∈ C.U, C.Θ η x.val = u
  density : ∀ x ∈ closure S.Ω₂, ∀ u ∈ (C.e x.val).target, ν u < R' →
    1 / 2 ≤ 1 + C.ωp x.val u ∧ 1 / 2 ≤ 1 + C.ωm x.val u

/-- Existence of an admissible radius (BB pp. 574-576): the
chart-image radius is the tube lemma for `isOpen_T` (`exists_gauge_image_radius`), the density
threshold is the lifted-chart field `density_bounds`. -/
theorem exists_admissibleRadius (S : H2.LocDoubling C.Carrier) (T : H2.TruncDist S)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν) {τ r : ℝ} (hτ : 0 < τ)
    (hr : 0 < r) : ∃ R' : ℝ, C.IsAdmissibleRadius S T ν τ r R' := by
  have hK : IsCompact (Carrier.val '' closure S.Ω₂ : Set (Fin (n + m) → ℝ)) :=
    S.cpt.image Carrier.continuous_val
  have hKU : (Carrier.val '' closure S.Ω₂ : Set (Fin (n + m) → ℝ)) ⊆ C.U := by
    rintro _ ⟨x, -, rfl⟩
    exact x.val_mem
  obtain ⟨Rimg, hRimg, himg⟩ := C.exists_gauge_image_radius hν hK hKU
  obtain ⟨_, _, Cd, r0, _, _, hCd, hr0, -, hdens⟩ := C.density_bounds _ hK hKU
  have hε : 0 < min r0 (1 / (2 * Cd)) := lt_min hr0 (by positivity)
  obtain ⟨Rd, hRd, hdball⟩ := exists_gauge_lt_subset_of_mem_nhds_zero C.G hν
    (Metric.ball_mem_nhds (0 : Fin (n + m) → ℝ) hε)
  have hθ := T.θ₁_pos
  have hθτ : 0 < T.θ₁ * τ := by positivity
  refine ⟨min (min (T.θ₁ * r / 4) (T.θ₁ * τ / 4)) (min Rimg Rd), ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min (by positivity) (by positivity)) (lt_min hRimg hRd)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · calc _ ≤ T.θ₁ * τ / 4 := (min_le_left _ _).trans (min_le_right _ _)
      _ < T.θ₁ * τ / 2 := by linarith
  · intro x hx u hu
    exact himg x.val ⟨x, hx, rfl⟩ u (hu.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  · intro x hx u hu hνu
    have hνd : ν u < Rd := hνu.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hu' : u ∈ ball (0 : Fin (n + m) → ℝ) (min r0 (1 / (2 * Cd))) := hdball u hνd
    rw [mem_ball, dist_zero_right] at hu'
    have hu0 : ‖u‖ < r0 := hu'.trans_le (min_le_left _ _)
    have hu1 : ‖u‖ < 1 / (2 * Cd) := hu'.trans_le (min_le_right _ _)
    obtain ⟨h1, h2⟩ := hdens x.val ⟨x, hx, rfl⟩ u hu hu0
    have h3 : Cd * ‖u‖ < 1 / 2 := by
      calc Cd * ‖u‖ < Cd * (1 / (2 * Cd)) := mul_lt_mul_of_pos_left hu1 hCd
        _ = 1 / 2 := by field_simp
    exact ⟨by linarith [neg_abs_le (C.ωp x.val u)], by linarith [neg_abs_le (C.ωm x.val u)]⟩

namespace IsAdmissibleRadius

variable {C} {S : H2.LocDoubling C.Carrier} {T : H2.TruncDist S}
  {ν : (Fin (n + m) → ℝ) → ℝ} {τ r R' R'' : ℝ}

/-- `R' ≤ θ₁ r` (the cutoff-radius condition of Data D1). -/
theorem le_θ₁_mul (h : C.IsAdmissibleRadius S T ν τ r R') (hr : 0 < r) : R' ≤ T.θ₁ * r := by
  have := h.le_cover
  have hθ := T.θ₁_pos
  nlinarith [mul_pos hθ hr]

/-- Points of the radial support are `d`-close: `d'(x, y) < R'`
implies `d(x, y) < r / 4` (so the supported shell lies inside the doubled ball). -/
theorem dist_lt_quarter (hT : C.IsRhoTruncation S ν τ T) (h : C.IsAdmissibleRadius S T ν τ r R')
    {x y : C.Carrier} (hxy : T.d' x y < R') : dist x y < r / 4 :=
  hT.dist_lt_of_d'_lt (ρ' := r / 4) (by linarith [h.le_cover])

/-- The radial support of the cutoff at a point of `U_j = B(z, r)`
lies inside the doubled ball `U_j^{(2)} = B(z, 2r)` (used for Data D3). -/
theorem mem_ball_two_mul (hT : C.IsRhoTruncation S ν τ T)
    (h : C.IsAdmissibleRadius S T ν τ r R') (hr : 0 < r) {z x y : C.Carrier}
    (hx : x ∈ ball z r) (hxy : T.d' x y < R') : y ∈ ball z (2 * r) := by
  have h1 := h.dist_lt_quarter hT hxy
  have h2 := mem_ball.mp hx
  rw [mem_ball]
  calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ = dist x y + dist x z := by rw [dist_comm y x]
    _ < 2 * r := by linarith

/-- Reconstruction support: if `x ∈ B(z, r/4)` and `d'(x, y) < R'`
then `y ∈ B(z, r/2)` (used in the finite reconstruction formula). -/
theorem mem_ball_half (hT : C.IsRhoTruncation S ν τ T) (h : C.IsAdmissibleRadius S T ν τ r R')
    {z x y : C.Carrier} (hx : x ∈ ball z (r / 4)) (hxy : T.d' x y < R') :
    y ∈ ball z (r / 2) := by
  have h1 := h.dist_lt_quarter hT hxy
  have h2 := mem_ball.mp hx
  rw [mem_ball]
  calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ = dist x y + dist x z := by rw [dist_comm y x]
    _ < r / 2 := by linarith

/-- Inside the radial support the truncation distance is `ρ`:
`d'(x, y) < R' ↔ ρ(x, y) < R'`, so the small truncations are exactly the original
`ρ`-truncations. -/
theorem d'_lt_iff_rho_lt (hT : C.IsRhoTruncation S ν τ T) (h : C.IsAdmissibleRadius S T ν τ r R')
    {x y : C.Carrier} : T.d' x y < R' ↔ C.rho ν x y < R' := by
  have hθ := T.θ₁_pos
  have hpos := h.pos
  have hlt := h.lt_trunc
  exact hT.d'_lt_iff_rho_lt (by nlinarith)

end IsAdmissibleRadius

end LiftedChart

end RothschildStein.P1

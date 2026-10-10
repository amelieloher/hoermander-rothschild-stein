-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.AffineReparametrization
public import HeatKernel.Geometry.NearGeodesic
public import HeatKernel.Geometry.HorizontalChainRule

/-! Distance bounds along horizontal curves with bounded control speed. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace HeatKernel

/-- A horizontal sub-arc with control speed at most one has endpoint distance at most
its parameter length. -/
theorem IsHorizontalCurveOn.subarc_distance_le_of_controlNorm_le_one {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {u v s t : ℝ} (h : IsHorizontalCurveOn X γ a u v)
    (hus : u ≤ s) (hst : s ≤ t) (htv : t ≤ v)
    (ha : ∀ r ∈ Icc s t, controlNorm a r ≤ 1) :
    horizontalL2Distance X (γ s) (γ t) ≤ ENNReal.ofReal (t - s) := by
  apply (h.subarc_distance_le hus hst htv).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ r in Icc s t, controlNorm a r) ≤ ∫ _r in Icc s t, (1 : ℝ) := by
      apply integral_mono_ae (h.integrable_norm.mono_set ?_) (integrableOn_const ?_)
      · exact ae_restrict_of_forall_mem measurableSet_Icc ha
      · intro r hr
        exact ⟨hus.trans hr.1, hr.2.trans htv⟩
      · exact measure_Icc_lt_top.ne
    _ = t - s := by simp [sub_nonneg.mpr hst]

/-- Finite positive horizontal distance has almost minimizing curves whose ordered
sub-arcs have distance bounded by their parameter length. -/
theorem exists_horizontal_nearGeodesic_with_subarc_bound {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {x y : Fin N → ℝ}
    (hd0 : 0 < horizontalL2Distance X x y) (hdf : horizontalL2Distance X x y ≠ ⊤)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ℓ : ℝ) (γ : ℝ → (Fin N → ℝ)) (a : Fin q → ℝ → ℝ),
      0 < ℓ ∧ ℓ < (1 + η) * (horizontalL2Distance X x y).toReal ∧
      γ 0 = x ∧ γ ℓ = y ∧ IsHorizontalCurveOn X γ a 0 ℓ ∧
      (∀ r, controlNorm a r ≤ 1) ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ ℓ →
        horizontalL2Distance X (γ s) (γ t) ≤ ENNReal.ofReal (t - s)) := by
  obtain ⟨ℓ, γ, a, hℓ, hlength, hx, hy, hγ, ha, _⟩ :=
    exists_horizontal_nearGeodesic hd0 hdf hη
  exact ⟨ℓ, γ, a, hℓ, hlength, hx, hy, hγ, ha,
    fun s t hs hst ht => hγ.subarc_distance_le_of_controlNorm_le_one hs hst ht
      (fun r _ => ha r)⟩

end HeatKernel

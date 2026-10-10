-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.NormalizedCurve

/-! Horizontal curves with bounded controls and duration close to the control distance. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace HeatKernel

/-- Any strict real upper bound on the horizontal distance is also a strict upper bound
on the duration of a joining horizontal curve with control norm at most one. -/
theorem exists_horizontalCurve_lt_of_distance_lt {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {x y : Fin N → ℝ} {R : ℝ}
    (hd : horizontalL2Distance X x y < ENNReal.ofReal R) :
    ∃ (ℓ : ℝ) (γ : ℝ → (Fin N → ℝ)) (b : Fin q → ℝ → ℝ),
      0 < ℓ ∧ ℓ < R ∧ γ 0 = x ∧ γ ℓ = y ∧ IsHorizontalCurveOn X γ b 0 ℓ ∧
      (∀ t, controlNorm b t ≤ 1) ∧ (∫ t in Icc (0 : ℝ) ℓ, controlNorm b t) < R := by
  obtain ⟨r, hr, hrR⟩ := sInf_lt_iff.mp hd
  rcases hr with ⟨γ, a, hac, hzero, hone, hmeas, hint, hderiv, rfl⟩
  let L := ∫ t in Icc (0 : ℝ) 1, controlNorm a t
  have hL : 0 ≤ L := integral_nonneg fun t => Real.sqrt_nonneg _
  have hLR : L < R := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hL).mp hrR
  let ε := (R - L) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have h : IsHorizontalCurveOn X γ a 0 1 := ⟨hac, hmeas, hint, hderiv⟩
  obtain ⟨e, b, _, hc, hb, hlen, he⟩ := h.normalize hε
  have hezero : e 0 = 0 := by simpa using he 0 (by norm_num)
  have heone : e 1 = L + ε := by
    have hconst : IntegrableOn (fun _ : ℝ => ε) (Icc (0 : ℝ) 1) :=
      integrableOn_const (by simp [Real.volume_Icc])
    rw [he 1 (by norm_num)]
    change (∫ u in Icc (0 : ℝ) 1, controlNorm a u + ε) = L + ε
    rw [integral_add h.integrable_norm hconst, setIntegral_const, Real.volume_real_Icc]
    norm_num [L]
  refine ⟨e 1, γ ∘ e.symm, b, ?_, ?_, ?_, ?_, ?_, hb, ?_⟩
  · rw [heone]
    linarith
  · rw [heone]
    dsimp [ε]
    linarith
  · change γ (e.symm 0) = x
    have hh : e.symm 0 = 0 := (congrArg e.symm hezero.symm).trans (e.symm_apply_apply 0)
    rw [hh, hzero]
  · simpa only [Function.comp_apply, e.symm_apply_apply] using hone
  · simpa only [hezero] using hc
  · rw [hezero] at hlen
    exact hlen.trans_lt hLR

/-- Finite positive horizontal distance has horizontal near-geodesics with control norm
at most one and arbitrarily small multiplicative excess in duration and length. -/
theorem exists_horizontal_nearGeodesic {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {x y : Fin N → ℝ}
    (hd0 : 0 < horizontalL2Distance X x y) (hdf : horizontalL2Distance X x y ≠ ⊤)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ℓ : ℝ) (γ : ℝ → (Fin N → ℝ)) (b : Fin q → ℝ → ℝ),
      0 < ℓ ∧ ℓ < (1 + η) * (horizontalL2Distance X x y).toReal ∧
      γ 0 = x ∧ γ ℓ = y ∧ IsHorizontalCurveOn X γ b 0 ℓ ∧
      (∀ t, controlNorm b t ≤ 1) ∧
      (∫ t in Icc (0 : ℝ) ℓ, controlNorm b t) < (1 + η) * (horizontalL2Distance X x y).toReal := by
  apply exists_horizontalCurve_lt_of_distance_lt
  have hd : 0 < (horizontalL2Distance X x y).toReal := ENNReal.toReal_pos hd0.ne' hdf
  calc
    horizontalL2Distance X x y = ENNReal.ofReal (horizontalL2Distance X x y).toReal :=
      (ENNReal.ofReal_toReal hdf).symm
    _ < ENNReal.ofReal ((1 + η) * (horizontalL2Distance X x y).toReal) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd.le).2 (by nlinarith)

end HeatKernel

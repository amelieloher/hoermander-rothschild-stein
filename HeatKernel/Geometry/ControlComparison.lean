-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.NearGeodesic
public import RothschildStein.G1.ChowConnectivity

/-! Comparison of Euclidean and componentwise horizontal control costs. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace HeatKernel

/-- Each control coordinate is bounded in absolute value by the Euclidean control norm. -/
theorem abs_control_le_controlNorm {q : ℕ} (a : Fin q → ℝ → ℝ) (i : Fin q) (t : ℝ) :
    |a i t| ≤ controlNorm a t := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (a j t)) (Finset.mem_univ i)

/-- A componentwise bound gives the usual square-root-of-dimension Euclidean bound. -/
theorem controlNorm_le_sqrt_mul {q : ℕ} (a : Fin q → ℝ → ℝ) (t δ : ℝ)
    (hδ : 0 ≤ δ) (ha : ∀ i, |a i t| ≤ δ) :
    controlNorm a t ≤ Real.sqrt q * δ := by
  have hs : ∑ i, a i t ^ 2 ≤ (q : ℝ) * δ ^ 2 := by
    calc
      ∑ i, a i t ^ 2 ≤ ∑ _ : Fin q, δ ^ 2 := Finset.sum_le_sum fun i _ => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ).2 (ha i)
      _ = (q : ℝ) * δ ^ 2 := by simp
  exact (Real.sqrt_le_sqrt hs).trans_eq (by rw [Real.sqrt_mul (Nat.cast_nonneg q), Real.sqrt_sq hδ])

/-- The Euclidean control norm of almost-everywhere measurable controls is measurable. -/
theorem aemeasurable_controlNorm {q : ℕ} {a : Fin q → ℝ → ℝ} {μ : Measure ℝ}
    (ha : ∀ i, AEMeasurable (a i) μ) : AEMeasurable (controlNorm a) μ := by
  exact Real.continuous_sqrt.measurable.comp_aemeasurable
    (Finset.aemeasurable_fun_sum Finset.univ fun i _ => (ha i).pow_const 2)

/-- A bounded-control horizontal curve gives a competitor for the componentwise distance
with cost equal to its parameter duration. -/
theorem controlDistance_le_of_bounded_horizontalCurve {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : IsHorizontalCurveOn X γ a 0 ℓ) (ha : ∀ t, controlNorm a t ≤ 1) :
    RothschildStein.controlDistance univ (fun _ : Fin q => 1) X (γ 0) (γ ℓ) ≤ ENNReal.ofReal ℓ := by
  have hc := h.affine_unit hℓ
  apply sInf_le
  refine ⟨ℓ, rfl, (fun u => γ (ℓ * u)), ⟨hℓ, ?_, fun _ _ => mem_univ _, ?_⟩, ?_, ?_⟩
  · simpa only [sub_zero, zero_add] using hc.absolutelyContinuous
  · refine ⟨fun i u => ℓ * a i (ℓ * u), ?_, ?_⟩
    · simpa only [sub_zero, zero_add] using hc.aemeasurable
    · filter_upwards [hc.hasDerivAt] with t ht
      refine ⟨fun i => ?_, ?_⟩
      · simp only [PNat.val_ofNat, pow_one, abs_mul, abs_of_pos hℓ]
        have hb := (abs_control_le_controlNorm a i (ℓ * t)).trans (ha _)
        nlinarith
      · simpa only [sub_zero, zero_add] using ht
  · simp
  · simp

/-- The componentwise control distance is no larger than the Euclidean length distance. -/
theorem controlDistance_le_horizontalL2Distance {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (x y : Fin N → ℝ) :
    RothschildStein.controlDistance univ (fun _ : Fin q => 1) X x y ≤ horizontalL2Distance X x y := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  by_cases hrt : r = ⊤
  · simp [hrt]
  have hR : horizontalL2Distance X x y < ENNReal.ofReal r.toReal := by
    simpa only [ENNReal.ofReal_toReal hrt] using hr
  obtain ⟨ℓ, γ, a, hℓ, hℓR, hzero, hone, hc, ha, _⟩ :=
    exists_horizontalCurve_lt_of_distance_lt hR
  have hb := controlDistance_le_of_bounded_horizontalCurve hℓ hc ha
  rw [hzero, hone] at hb
  exact hb.trans (by rw [← ENNReal.ofReal_toReal hrt]; exact ENNReal.ofReal_le_ofReal hℓR.le)

/-- Each componentwise competitor bounds the Euclidean distance by its dimension factor. -/
theorem horizontalL2Distance_le_of_controlledCurve {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)} {δ : ℝ}
    (h : RothschildStein.isControlledCurve univ (fun _ : Fin q => 1) X δ γ) :
    horizontalL2Distance X (γ 0) (γ 1) ≤ ENNReal.ofReal (Real.sqrt q * δ) := by
  rcases h with ⟨hδ, hac, _, a, hmeas, hderiv⟩
  have hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), controlNorm a t ≤ Real.sqrt q * δ := by
    filter_upwards [hderiv] with t ht
    apply controlNorm_le_sqrt_mul a t δ hδ.le
    simpa only [PNat.val_ofNat, pow_one] using ht.1
  have hint : IntegrableOn (controlNorm a) (Icc (0 : ℝ) 1) := by
    apply (integrableOn_const (C := Real.sqrt q * δ) (by simp [Real.volume_Icc])).mono'
      (aemeasurable_controlNorm hmeas).aestronglyMeasurable
    filter_upwards [hbound] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ controlNorm a t from Real.sqrt_nonneg _)] using ht
  have hc : IsHorizontalCurveOn X γ a 0 1 :=
    ⟨hac, hmeas, hint, hderiv.mono fun _ ht => ht.2⟩
  apply (horizontalL2Distance_le_controlLength hc).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    ∫ t in Icc (0 : ℝ) 1, controlNorm a t ≤ ∫ _ in Icc (0 : ℝ) 1, Real.sqrt q * δ :=
      integral_mono_ae hint (integrableOn_const (by simp [Real.volume_Icc])) hbound
    _ = Real.sqrt q * δ := by simp [Real.volume_real_Icc]

/-- The Euclidean length distance is at most the componentwise distance times the
square root of the positive number of fields. -/
theorem horizontalL2Distance_le_sqrt_mul_controlDistance {N q : ℕ} (hq : 0 < q)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (x y : Fin N → ℝ) :
    horizontalL2Distance X x y ≤ ENNReal.ofReal (Real.sqrt q) *
      RothschildStein.controlDistance univ (fun _ : Fin q => 1) X x y := by
  have hs : ENNReal.ofReal (Real.sqrt q) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.sqrt_pos.2 (Nat.cast_pos.2 hq)
  unfold RothschildStein.controlDistance
  rw [sInf_eq_iInf, ENNReal.mul_iInf_of_ne hs ENNReal.ofReal_ne_top]
  apply le_iInf
  intro r
  rw [ENNReal.mul_iInf_of_ne hs ENNReal.ofReal_ne_top]
  apply le_iInf
  rintro ⟨δ, rfl, γ, hc, hzero, hone⟩
  have hb := horizontalL2Distance_le_of_controlledCurve hc
  rw [hzero, hone, ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hb
  exact hb

/-- Smooth bracket-generating fields have finite Euclidean horizontal control distance. -/
theorem horizontalL2Distance_ne_top_of_bracketSpansOn {N q : ℕ} (hq : 0 < q)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hrank : RothschildStein.bracketSpansOn univ X)
    (x y : Fin N → ℝ) : horizontalL2Distance X x y ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (horizontalL2Distance_le_sqrt_mul_controlDistance hq X x y)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (RothschildStein.G1.controlDistance_ne_top_of_bracketSpansOn isOpen_univ isPreconnected_univ
      (fun _ => 1) X (fun i => (hX i).contDiffOn) hrank (mem_univ x) (mem_univ y))

end HeatKernel

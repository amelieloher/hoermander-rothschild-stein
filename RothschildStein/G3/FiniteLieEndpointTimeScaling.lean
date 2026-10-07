-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFieldLinearity
public import RothschildStein.G3.ExponentialFlowMaps
public import RothschildStein.G1.FlowUniqueness
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- The same actual family agrees under coefficient/time scaling, by ODE
uniqueness on the original open spatial domain. -/
theorem finiteLie_endpoint_time_scaling {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ ρ : ℝ} (hκ : 0 < κ) (hρκ : |ρ| < κ)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),t) ∈ Ω ∧
          HasDerivAt (fun v => Φ ((D.basis.equivFun z,x),v))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),t))) t)
    (f : formalSpan a s p)
    (hκf : D.basis.equivFun (κ • f) ∈ ball 0 σ)
    (hρf : D.basis.equivFun (ρ • f) ∈ ball 0 σ)
    {x : Fin N → ℝ} (hx : x ∈ Ω₀) :
    Φ ((D.basis.equivFun (κ • f),x),ρ/κ) =
      finiteLieTimeOneMap Φ (D.basis.equivFun (ρ • f),x) := by
  have ha := hODE (κ • f) hκf x hx
  have hb := hODE (ρ • f) hρf x hx
  have hr : |ρ/κ| < 1 := by
    rw [abs_div,abs_of_pos hκ]
    exact (div_lt_one hκ).mpr hρκ
  have ht : ∀ t ∈ Ioo (-2 : ℝ) 2, (ρ/κ)*t ∈ Ioo (-2 : ℝ) 2 := by
    intro t ht
    apply abs_lt.mp
    rw [abs_mul]
    have htv : |t| < 2 := abs_lt.mpr ht
    exact (mul_le_mul_of_nonneg_right hr.le (abs_nonneg t)).trans_lt (by simpa using htv)
  have hscale : ∀ y, (ρ/κ) • finiteLieField D X (κ • f) y = finiteLieField D X (ρ • f) y := by
    intro y
    have he := congrArg (fun Z : (Fin N → ℝ) → (Fin N → ℝ) => Z y)
      ((finiteLieFieldLinear D X).map_smul κ f)
    have hf := congrArg (fun Z : (Fin N → ℝ) → (Fin N → ℝ) => Z y)
      ((finiteLieFieldLinear D X).map_smul ρ f)
    simp only [finiteLieFieldLinear_apply,Pi.smul_apply] at he hf
    rw [he,hf,smul_smul,div_mul_cancel₀ ρ hκ.ne']
  have he := G1.integralCurve_eqOn Ω.isOpen (finiteLieField_contDiffOn D Ω X hX (ρ • f))
    (α := fun t => Φ ((D.basis.equivFun (κ • f),x),(ρ/κ)*t))
    (β := fun t => Φ ((D.basis.equivFun (ρ • f),x),t))
    (by norm_num : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2) ?_ ?_ ?_
  · simpa only [mul_one,finiteLieTimeOneMap] using he (by norm_num : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2)
  · intro t htt
    refine ⟨?_,(ha.2 _ (ht t htt)).1⟩
    have hinner : HasDerivAt (fun v : ℝ => (ρ/κ)*v) (ρ/κ) t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul (ρ/κ)
    have hd := ((ha.2 _ (ht t htt)).2).scomp t hinner
    simpa only [Function.comp_def,mul_one,hscale] using hd
  · intro t htt
    exact ⟨(hb.2 t htt).2,(hb.2 t htt).1⟩
  · simp only [mul_zero,ha.1,hb.1]
end RothschildStein.G3

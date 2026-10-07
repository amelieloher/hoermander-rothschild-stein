-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.InverseControlCoordinates
public import RothschildStein.G1.ControlledVariation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- On an actual inverse neighborhood, an absolutely continuous
short controlled curve has the signed coordinate displacement bound.
The chain rule and scalar FTC use the measurable controls only almost
everywhere (BB Prop 9.52, (9.51), pp. 448–449). -/
theorem lifted_controlledCurve_coordinate_variation_on_interval {m n : ℕ}
    {Ω U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin m → ℕ+) (B : Fin n → Fin m)
    (Ψ : (Fin n → ℝ) → (Fin n → ℝ)) (hΨ : ContDiffOn ℝ 1 Ψ U)
    {γ : ℝ → (Fin n → ℝ)} {r b D L : ℝ} (hr : 0 < r) (hb : 0 ≤ b)
    (hb1 : 2 * b ≤ 1) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hγ : isControlledCurve Ω w Z (2 * b * r) γ)
    (hdet : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ U → frameDet Z B (γ τ) ≠ 0)
    (hframe : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ U → ∀ J j,
      |frameCoefficient Z B (Z J) j (γ τ)| ≤
        D * r ^ (((w (B j) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)))
    (hT : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ U → ∀ i j,
      |fderiv ℝ Ψ (γ τ) (Z (B j) (γ τ)) i| ≤
        L * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ))) :
    ∀ σ ∈ Icc (0 : ℝ) 1, ∀ τ ∈ Icc (0 : ℝ) 1,
      (∀ v ∈ uIcc σ τ, γ v ∈ U) → ∀ i,
      |Ψ (γ τ) i - Ψ (γ σ) i| ≤
        (2 * (m : ℝ) * n * D * L) * b * r ^ (w (B i) : ℕ) * |τ - σ| := by
  intro σ hσ τ hτ hpatch i
  have hf : ContDiffOn ℝ 1 (fun y => Ψ y i) U :=
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (hΨ.of_le (by simp))
  have hsub : uIcc σ τ ⊆ Icc (0 : ℝ) 1 := ordConnected_Icc.uIcc_subset hσ hτ
  have hacγ := hγ.2.1.mono (by simpa only [uIcc_of_le zero_le_one] using hsub)
  have hacτ := G1.absolutelyContinuousOnInterval_comp_contDiffOn hU hf hacγ hpatch
  obtain ⟨a, _hmeas, ha⟩ := hγ.2.2.2
  have hae := (ae_restrict_iff' measurableSet_Icc).mp ha
  let C := (2 * (m : ℝ) * n * D * L) * b * r ^ (w (B i) : ℕ)
  have hm : ‖∫ s in σ..τ, deriv (fun v => Ψ (γ v) i) s‖ ≤ C * |τ - σ| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [hae] with s hs htime
    have hsseg := uIoc_subset_uIcc htime
    have hs1 := hsub hsseg
    have hsU := hpatch s hsseg
    have hdΨ := ((hΨ.contDiffAt (hU.mem_nhds hsU)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt s (hs hs1).2
    have hd := (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hdΨ
    have hd' : HasDerivAt (fun v => Ψ (γ v) i)
        (fderiv ℝ Ψ (γ s) (∑ j, a j s • Z j (γ s)) i) s := hd
    rw [hd'.deriv, Real.norm_eq_abs]
    simpa only [Fintype.card_fin] using weighted_control_inverse_coordinate_bound Z w B
      (fderiv ℝ Ψ (γ s)) (hdet s hs1 hsU) hr hb hb1 hD hL (hframe s hs1 hsU) (hT s hs1 hsU)
      (fun j => a j s) (hs hs1).1 i
  have hFTC : (∫ s in σ..τ, deriv (fun v => Ψ (γ v) i) s) =
      Ψ (γ τ) i - Ψ (γ σ) i := hacτ.integral_deriv_eq_sub
  rw [hFTC] at hm
  simpa only [Real.norm_eq_abs] using hm

end RothschildStein.G4

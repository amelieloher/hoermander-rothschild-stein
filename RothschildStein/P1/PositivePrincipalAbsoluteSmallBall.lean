-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ModelInputNearBounds
public import RothschildStein.P1.UniformModelSmallBallBound
public import RothschildStein.P1.PrincipalCutoffKernel
public import RothschildStein.P1.ContinuityPositive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- Every actual positive principal term has a
uniform O(ε) absolute small-ball bound with both endpoint cutoffs retained. -/
theorem exists_positivePrincipal_uniform_absoluteSmallBall_bound
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (hd : t.degree ≤ 1)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ‖∫ u in {u | ν u ≤ ε}, ‖t.cutoffModelKernel ξ ((C.e ξ).symm (-u)) u *
        C.reflectedTransport ξ ψ u‖‖ ≤ A * ε := by
  obtain ⟨δ, L, hδ, hδ1, hL, hKL, hp⟩ := C.exists_inputModel_near_parameter_range hK hKU
  obtain ⟨B, hB, hb⟩ := C.exists_reflectedTransport_near_bound ψ hK hKU δ
  have hWB := t.cutoffModelKernel_hasWeightedBounds (hF.pole_smooth t.star)
    (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star)
  rw [hF.G_eq] at hWB
  obtain ⟨M, hM, hm⟩ := hWB L hL 1
  apply uniformModel_smallBall_bound C.G hν
    (fun ξ u => ‖t.cutoffModelKernel ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u‖)
    hδ (mul_nonneg hM hB)
  intro ξ hξ u hu hsmall
  have hρ1 : kgauge C.G u ≤ 1 := hsmall.trans hδ1
  have hnorm : ‖t.cutoffModelKernel ξ ((C.e ξ).symm (-u)) u‖ ≤
      M * kgauge C.G u ^ ((2 - (C.G.homogeneousDimension : ℤ) - t.degree : ℤ) : ℝ) := by
    simpa only [← Real.rpow_intCast, Real.norm_eq_abs] using
      (hm ξ (hKL hξ) ((C.e ξ).symm (-u)) (hp ξ hξ u hsmall) u hu hρ1).1
  have hexp : 1 - (C.G.homogeneousDimension : ℝ) ≤
      ((2 - (C.G.homogeneousDimension : ℤ) - t.degree : ℤ) : ℝ) := by
    have hdR : (t.degree : ℝ) ≤ 1 := by exact_mod_cast hd
    push_cast
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_ge (kgauge_pos C.G hu) hρ1 hexp
  have hk : ‖t.cutoffModelKernel ξ ((C.e ξ).symm (-u)) u‖ ≤
      M * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℝ)) :=
    hnorm.trans (mul_le_mul_of_nonneg_left hpow hM)
  rw [norm_norm, norm_mul]
  calc
    _ ≤ (M * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℝ))) * B :=
      mul_le_mul hk (hb ξ hξ u hsmall) (norm_nonneg _)
        (mul_nonneg hM (Real.rpow_nonneg (kgauge_nonneg C.G u) _))
    _ = (M * B) * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℝ)) := by ring

end RothschildStein.P1.LiftedChart

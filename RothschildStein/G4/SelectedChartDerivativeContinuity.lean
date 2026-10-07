-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedFlowDerivativeBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace RothschildStein.G4

/-- Joint smoothness of the actual time-one flow implies joint
continuity of the selected spatial derivative at zero coefficients.
This verifies the derivative-continuity needed for the local chart estimate for
fixed systems (BB pp. 450–458 and Theorem 9.11, p. 404). -/
theorem selected_chart_fderiv_continuousAt_zero {m n : ℕ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {δ : ℝ} (hδ : 0 < δ)
    (Φ : (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2))
    {x : Fin n → ℝ} (hx : x ∈ U) :
    ContinuousAt (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      fderiv ℝ (fun u => Φ ((Fin.append u 0, q.2), 1)) q.1) (0, x) := by
  let H : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
    fun q => Φ (((selectedCoefficientInclusion n m) q.1, q.2), 1)
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) H (0, x) := by
    have hp : ((0, x), (1 : ℝ)) ∈ (ball (0 : Fin (n + m) → ℝ) δ ×ˢ U) ×ˢ Ioo (-2) 2 :=
      ⟨⟨mem_ball_self hδ, hx⟩, by constructor <;> norm_num⟩
    have hh := hΦ.contDiffAt (((isOpen_ball.prod hU).prod isOpen_Ioo).mem_nhds hp)
    have hh' : ContDiffAt ℝ (⊤ : ℕ∞) Φ
        (((selectedCoefficientInclusion n m) 0, x), 1) := by
      simpa only [map_zero] using hh
    exact hh'.comp (0, x)
      ((((selectedCoefficientInclusion n m).contDiff.contDiffAt.comp (0, x)
        contDiffAt_fst).prodMk contDiffAt_snd).prodMk contDiffAt_const)
  let i : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
    ContinuousLinearMap.inl ℝ _ _
  have hc : ContinuousAt (fun q => (fderiv ℝ H q).comp i) (0, x) :=
    ((hs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuousAt).clm_comp continuousAt_const
  have hd : ∀ᶠ q in 𝓝 (0, x), DifferentiableAt ℝ H q :=
    ((hs.of_le (m := 1) (by simp)).eventually (by norm_num)).mono
      (fun q hq => hq.differentiableAt (by norm_num))
  apply hc.congr_of_eventuallyEq
  filter_upwards [hd] with q hq
  have hi : HasFDerivAt (fun u : Fin n → ℝ => (u, q.2)) i q.1 :=
    hasFDerivAt_prodMk_left q.1 q.2
  have hh : HasFDerivAt (fun u : Fin n → ℝ => H (u, q.2))
      ((fderiv ℝ H q).comp i) q.1 :=
    hq.hasFDerivAt.comp (f := fun u : Fin n → ℝ => (u, q.2)) (g := H) q.1 hi
  have he := hh.fderiv
  have ha : (fun u => Φ ((Fin.append u 0, q.2), 1)) = (fun u => H (u, q.2)) := by
    funext u
    rw [selectedCoefficient_append_affine]
    have hzero : Fin.append (0 : Fin n → ℝ) (0 : Fin m → ℝ) = 0 := by
      ext j
      exact Fin.addCases (fun j => by simp) (fun j => by simp) j
    simp only [hzero, add_zero, H]
  rw [ha]
  exact he

end RothschildStein.G4

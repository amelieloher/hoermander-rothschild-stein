-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SignedEndpointFromModelError
public import RothschildStein.G1.QuasiLogPowerFactor
public import RothschildStein.G1.FiniteLieCoefficientDerivative
public import RothschildStein.G3.ActualQuasiExponentialPoints
public import RothschildStein.G3.DilatedInputCoordinates
public import RothschildStein.G3.FiniteLieFieldWords
public import RothschildStein.G3.ZeroCoefficientFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.G1
open G3

/-- The genuine weighted quasiexponential and its genuine inverse
have a signed-root chart with the actual bracket as leading derivative.
The inputs are the finite Lie ODE and the point-error estimates for the finite Lie model. -/
theorem actual_signed_quasi_regular_of_point_error {a s n : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s)
    (I : List (Fin a)) (hne : I ≠ []) (hI : wordWeight p I ≤ s)
    {Ω U : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {A : Set (Fin (freeDimension a s p) → ℝ)} (hA : IsOpen A) (hz : 0 ∈ A)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((A ×ˢ U) ×ˢ Ioo (-2 : ℝ) 2))
    (hODE : ∀ f : formalSpan a s p, D.basis.equivFun f ∈ A → ∀ x ∈ U,
      Φ ((D.basis.equivFun f, x), 0) = x ∧ ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun v => Φ ((D.basis.equivFun f, x), v))
          (finiteLieField D X f (Φ ((D.basis.equivFun f, x), t))) t ∧
        Φ ((D.basis.equivFun f, x), t) ∈ Ω)
    (Ψ : Fin a → ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    {η M : ℝ} (hη : 0 < η)
    (hQp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin n → ℝ) × ℝ => quasiExponentialPointMap p Ψ I q.2 q.1)
      (U ×ˢ Ioo (-η) η))
    (hQm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin n → ℝ) × ℝ => inverseQuasiExponentialPointMap p Ψ I q.2 q.1)
      (U ×ˢ Ioo (-η) η))
    (hp : ∀ x ∈ U, ∀ t ∈ Ioo (-η) η,
      ‖quasiExponentialPointMap p Ψ I t x -
        Φ ((dilatedInputCoordinates D (quasiExponentialLog I) t, x), 1)‖ ≤ M * |t| ^ (s + 1))
    (hm : ∀ x ∈ U, ∀ t ∈ Ioo (-η) η,
      ‖inverseQuasiExponentialPointMap p Ψ I t x -
        Φ ((dilatedInputCoordinates D (-(quasiExponentialLog I : formalSpan a s p)) t, x), 1)‖ ≤
          M * |t| ^ (s + 1))
    {x : Fin n → ℝ} (hx : x ∈ U) :
    let Gp := fun q : (Fin n → ℝ) × ℝ => quasiExponentialPointMap p Ψ I q.2 q.1 - q.1
    let Gm := fun q : (Fin n → ℝ) × ℝ => inverseQuasiExponentialPointMap p Ψ I q.2 q.1 - q.1
    ContDiffAt ℝ 1 (signedRootEndpoint (wordWeight p I) Gp Gm) (0, x) ∧
      HasFDerivAt (signedRootEndpoint (wordWeight p I) Gp Gm)
        ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) +
          (ContinuousLinearMap.toSpanSingleton ℝ (wordBracket X I x)).comp
            (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))) (0, x) := by
  intro Gp Gm
  let F := fun q : (Fin (freeDimension a s p) → ℝ) × (Fin n → ℝ) => Φ (q, 1)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (A ×ˢ U) :=
    hΦ.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun _ hq => ⟨hq, by norm_num⟩)
  have hzero : ∀ y, (0, y) ∈ A ×ˢ U → F (0, y) = y := by
    intro y hy
    have hh := hODE 0 (by simpa only [map_zero] using hz) y hy.2
    simp only [map_zero] at hh
    exact finiteLieTimeOneMap_zero_of_finiteLie_ode D X Φ y hh.1
      (fun t ht => (hh.2 t ht).1)
  obtain ⟨H, hH, hH₀, heH⟩ := exists_quasi_log_coordinate_power_factor D hs I
  have hk : 0 < wordWeight p I :=
    (List.length_pos_iff.mpr hne).trans_le (length_le_weight p I)
  have hneg : ∀ t, dilatedInputCoordinates D (-(quasiExponentialLog I : formalSpan a s p)) t =
      -(t ^ wordWeight p I • H t) := by
    intro t
    rw [← heH]
    ext j
    simp only [dilatedInputCoordinates, coordinateDilation, map_neg, Pi.neg_apply, mul_neg]
  have hep : ∀ q ∈ U ×ˢ Ioo (-η) η,
      ‖Gp q - (F (q.2 ^ wordWeight p I • H q.2, q.1) - q.1)‖ ≤ M * |q.2| ^ (s + 1) := by
    intro q hq
    have he : Gp q - (F (q.2 ^ wordWeight p I • H q.2, q.1) - q.1) =
        quasiExponentialPointMap p Ψ I q.2 q.1 - F (q.2 ^ wordWeight p I • H q.2, q.1) := by
      dsimp [Gp]
      abel
    rw [he, ← heH]
    exact hp q.1 hq.1 q.2 hq.2
  have hem : ∀ q ∈ U ×ˢ Ioo (-η) η,
      ‖Gm q - (F (-(q.2 ^ wordWeight p I • H q.2), q.1) - q.1)‖ ≤ M * |q.2| ^ (s + 1) := by
    intro q hq
    have he : Gm q - (F (-(q.2 ^ wordWeight p I • H q.2), q.1) - q.1) =
        inverseQuasiExponentialPointMap p Ψ I q.2 q.1 - F (-(q.2 ^ wordWeight p I • H q.2), q.1) := by
      dsimp [Gm]
      abel
    rw [he, ← hneg]
    exact hm q.1 hq.1 q.2 hq.2
  obtain ⟨hc, hd⟩ := signedRootEndpoint_regular_of_actual_endpoint_errors hk hI
    (hA.prod hU) F hF hzero H hH (hU.prod isOpen_Ioo) Gp Gm
    (hQp.sub contDiff_fst.contDiffOn) (hQm.sub contDiff_fst.contDiffOn) M hep hem x
    ⟨hz, hx⟩ ⟨hx, by simpa using hη⟩
  have hlead : fderiv ℝ (fun z => F (z, x)) 0 (H 0) = wordBracket X I x := by
    rw [hH₀]
    rw [finite_lie_timeOne_coefficient_derivative D hΩ hU hUΩ X hX hA hz Φ hΦ hODE hx]
    exact finiteLieField_word D ⟨Ω, hΩ⟩ X hX I hne hI (hUΩ hx)
  exact ⟨hc, by simpa only [hlead] using hd⟩

end RothschildStein.G1

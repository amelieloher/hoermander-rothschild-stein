-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.InverseFundamentalDerivative
public import RothschildStein.G1.SmoothDependenceMain

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The actual forward transported field has derivative minus the
transported Lie bracket, at every time on the finite local overlap
(BB Lemma 9.48, pp. 442–443). -/
theorem localFlow_transported_hasDerivAt_of_joint_contDiff
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (Z Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hend : Φ (x, -t) ∈ U) :
    HasDerivAt (fun v => (fderiv ℝ (fun y => Φ (y, v)) (Φ (x, -v))) (Y (Φ (x, -v))))
      (- (fderiv ℝ (fun y => Φ (y, t)) (Φ (x, -t)))
        (VectorField.lieBracket ℝ Z Y (Φ (x, -t)))) t := by
  let Ψ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ) := fun p => Φ (p.1, -p.2)
  have hneg : ∀ v ∈ Ioo (-τ) τ, -v ∈ Ioo (-τ) τ := by
    intro v hv
    constructor <;> linarith [hv.1, hv.2]
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (U ×ˢ Ioo (-τ) τ) :=
    hjoint.comp (contDiffOn_fst.prodMk contDiffOn_snd.neg)
      (fun p hp => ⟨hp.1, hneg p.2 hp.2⟩)
  have hsol : ∀ y ∈ U, Ψ (y, 0) = y ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Ψ (y, w)) ((-Z) (Ψ (y, v))) v ∧ Ψ (y, v) ∈ Ω := by
    intro y hy
    refine ⟨by simpa only [Ψ, neg_zero] using (hΦ y hy).1, ?_⟩
    intro v hv
    refine ⟨?_, ((hΦ y hy).2 (-v) (hneg v hv)).2⟩
    simpa only [Ψ, Pi.neg_apply, neg_one_smul, Function.comp_def] using
      (((hΦ y hy).2 (-v) (hneg v hv)).1.scomp v (hasDerivAt_neg v))
  have hA := localFlow_opposite_jacobian_hasDerivAt_of_joint_contDiff hΩ hU hZ.neg
    hτ Ψ hΨ hsol hx ht hend
  have hα := ((hsol x hx).2 t ht).1
  have hDY := ((hY.contDiffAt (hΩ.mem_nhds ((hsol x hx).2 t ht).2)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t hα
  have hh := hA.clm_apply hDY
  have hh' : HasDerivAt
      (fun v => (fderiv ℝ (fun y => Φ (y, v)) (Φ (x, -v))) (Y (Φ (x, -v))))
      ((fderiv ℝ (fun y => Φ (y, t)) (Φ (x, -t)))
        ((fderiv ℝ Z (Φ (x, -t))) (Y (Φ (x, -t)))) +
      -(fderiv ℝ (fun y => Φ (y, t)) (Φ (x, -t)))
        ((fderiv ℝ Y (Φ (x, -t))) (Z (Φ (x, -t))))) t := by
    simpa only [Ψ, neg_neg, fderiv_neg, fderiv_fun_neg, Pi.neg_apply,
      ContinuousLinearMap.comp_apply, neg_apply, map_neg, Function.comp_def] using hh
  convert hh' using 1
  simp only [VectorField.lieBracket, map_sub]
  abel

/-- The transported Lie-bracket differential identity for an actual
continuous local flow, under joint smooth dependence of the flow
(BB Lemma 9.48, pp. 442–443). -/
theorem localFlow_transported_hasDerivAt
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (Z Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hend : Φ (x, -t) ∈ U) :
    HasDerivAt (fun v => (fderiv ℝ (fun y => Φ (y, v)) (Φ (x, -v))) (Y (Φ (x, -v))))
      (- (fderiv ℝ (fun y => Φ (y, t)) (Φ (x, -t)))
        (VectorField.lieBracket ℝ Z Y (Φ (x, -t)))) t := by
  have hjoint := RothschildStein.G1.local_flow_contDiffOn hΩ hU hτ hZ hc
    (fun y hy => (hΦ y hy).1) (fun y hy s hs =>
      ⟨((hΦ y hy).2 s hs).2, ((hΦ y hy).2 s hs).1⟩)
  exact localFlow_transported_hasDerivAt_of_joint_contDiff hΩ hU Z Y hZ hY hτ Φ
    hjoint hΦ hx ht hend

end RothschildStein.G4

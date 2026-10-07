-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TransportedTaylorIntegral
public import RothschildStein.G4.JointAdjointJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Exact variable-time transported Taylor identity for an ACTUAL
parameter flow, written with the joint actual adjoint families. The open
time buffer is derived from the reverse-endpoint condition
(BB Lemma 9.48, pp. 442–443; NSW p. 127). -/
theorem parameterFlow_transported_taylor_integral_at_time {P : Type*} {N : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : Set P} {Ω : Set (Fin N → ℝ)} {U : Set (P × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    (Z Y : P × (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (A ×ˢ Ω))
    {τ : ℝ} (hτ : 1 < τ) (Φ : (P × (Fin N → ℝ)) × ℝ → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {p : P × (Fin N → ℝ)} (hp : p ∈ U)
    (hend : ∀ s ∈ Icc (0 : ℝ) 1, (p.1, Φ (p, -s)) ∈ U)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (q : ℕ) :
    (fderiv ℝ (fun y => Φ ((p.1, y), t)) (Φ (p, -t))) (Y (p.1, Φ (p, -t))) =
      (∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j * t ^ j / (j.factorial : ℝ)) •
        (((spatialBracketFamily Z)^[j] Y) p)) +
      (q.factorial : ℝ)⁻¹ • ∫ s in (0 : ℝ)..1,
        ((1 - s) ^ q * t ^ (q + 1) * (-1 : ℝ) ^ (q + 1)) •
          (fderiv ℝ (fun y => Φ ((p.1, y), s * t)) (Φ (p, -(s * t))))
            (((spatialBracketFamily Z)^[q + 1] Y) (p.1, Φ (p, -(s * t)))) := by
  let V : Set (Fin N → ℝ) := (fun y => (p.1, y)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hpV : p.2 ∈ V := hp
  let F : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ) := fun v => Φ ((p.1, v.1), v.2)
  have hFc : ContinuousOn F (V ×ˢ Ioo (-τ) τ) :=
    hc.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousOn
      (fun v hv => ⟨hv.1, hv.2⟩)
  have hZA : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => Z (p.1, y)) Ω :=
    hZ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨(hUA hp).1, hy⟩)
  have hYA : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => Y (p.1, y)) Ω :=
    hY.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨(hUA hp).1, hy⟩)
  have hFsol : ∀ y ∈ V, F (y, 0) = y ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => F (y, w)) (Z (p.1, F (y, v))) v ∧ F (y, v) ∈ Ω :=
    fun y hy => hΦ (p.1, y) hy
  have hrev : ContinuousOn (fun s => F (p.2, -s)) (Ioo (-τ) τ) :=
    hFc.comp (continuous_const.prodMk continuous_id.neg).continuousOn (fun s hs =>
      ⟨hpV, by constructor <;> linarith [hs.1, hs.2]⟩)
  let T := Ioo (-τ) τ ∩ (fun s => F (p.2, -s)) ⁻¹' V
  have hT : IsOpen T := hrev.isOpen_inter_preimage isOpen_Ioo hV
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, s * t ∈ T := by
    intro s hs
    have hst : s * t ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hs.1 ht.1, (mul_le_mul hs.2 ht.2 ht.1 (by norm_num)).trans_eq (one_mul _)⟩
    exact ⟨⟨by linarith [hst.1], by linarith [hst.2]⟩, hend _ hst⟩
  have he := localFlow_transported_taylor_integral hΩ hV
    (fun y => Z (p.1, y)) (fun y => Y (p.1, y)) hZA hYA
    (show 0 < τ by linarith) F hFc hFsol hpV hT inter_subset_left
    (fun s hs => hs.2) q hseg
  have hi : ∀ j, ∀ y, ((spatialBracketFamily Z)^[j] Y) (p.1, y) =
      ((VectorField.lieBracket ℝ (fun v => Z (p.1, v)))^[j] (fun v => Y (p.1, v))) y :=
    fun j y => congrFun (spatialBracketFamily_iterate_slice Z Y p.1 j) y
  dsimp only [F] at he
  simp only [hi]
  simpa only [Prod.mk.eta] using he

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.JointFlowSpatialDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Joint smoothness of the actual transported field kernel on
its reverse-endpoint open overlap. The premise is the exact proved joint
flow-smoothness interface (BB Lemma 9.48, pp. 441–443). -/
theorem transported_kernel_contDiffOn_of_joint_contDiff {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (P × E)} (hU : IsOpen U) {τ : ℝ}
    (Φ : (P × E) × ℝ → E)
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (Y : P × E → E) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y U) :
    let S := (U ×ˢ Ioo (-τ) τ) ∩
      {q | (q.1.1, Φ (q.1, -q.2)) ∈ U}
    IsOpen S ∧ ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => (fderiv ℝ (fun y => Φ ((q.1.1, y), q.2)) (Φ (q.1, -q.2)))
        (Y (q.1.1, Φ (q.1, -q.2)))) S := by
  intro S
  let D := U ×ˢ Ioo (-τ) τ
  have hD : IsOpen D := hU.prod isOpen_Ioo
  have hneg : MapsTo (fun q : (P × E) × ℝ => (q.1, -q.2)) D D := by
    intro q hq
    exact ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
  have hrev : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => Φ (q.1, -q.2)) D :=
    hjoint.comp (contDiffOn_fst.prodMk contDiffOn_snd.neg) hneg
  let Q : (P × E) × ℝ → P × E := fun q => (q.1.1, Φ (q.1, -q.2))
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q D := contDiffOn_fst.fst.prodMk hrev
  have hS : IsOpen S := hQ.continuousOn.isOpen_inter_preimage hD hU
  have hQS : MapsTo Q S U := fun q hq => hq.2
  have hQT : MapsTo (fun q => (Q q, q.2)) S D :=
    fun q hq => ⟨hq.2, hq.1.2⟩
  have hJ := (joint_flow_spatial_fderiv_contDiffOn hD hjoint).comp
    ((hQ.mono inter_subset_left).prodMk contDiffOn_snd) hQT
  exact ⟨hS, hJ.clm_apply (hY.comp (hQ.mono inter_subset_left) hQS)⟩

end RothschildStein.G4

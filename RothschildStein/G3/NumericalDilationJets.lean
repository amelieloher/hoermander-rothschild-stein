-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DilatedInputCoordinates
public import RothschildStein.G3.CompactAmbientJets
public import RothschildStein.G3.PositiveCompositionAt
public import RothschildStein.G3.FixedStateInputJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- The coefficient dilation is a polynomial jointly in scale and coefficients. -/
theorem coordinateDilation_joint_contDiff {d : ℕ} (w : Fin d → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin d → ℝ) => coordinateDilation w z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_fst.pow (w i)).mul (contDiff_apply ℝ ℝ i |>.comp contDiff_snd)

/-- A bounded coefficient set has one dilation jet budget, chosen before fields. -/
theorem exists_numerical_dilation_jet_bound {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (R : ℝ) (Q : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ f : formalSpan a s p, ‖D.basis.equivFun f‖ ≤ R →
      ∀ t : ℝ, |t| ≤ 1 → ∀ j, 1 ≤ j → j ≤ Q →
        ‖iteratedFDeriv ℝ j (dilatedInputCoordinates D f) t‖ ≤ A := by
  let J := fun z : ℝ × (Fin (freeDimension a s p) → ℝ) =>
    coordinateDilation D.weight z.1 z.2
  have hJ : ContDiff ℝ (⊤ : ℕ∞) J := coordinateDilation_joint_contDiff D.weight
  obtain ⟨C,hC,hjets⟩ := exists_compact_ambient_jet_bound J hJ
    ((isCompact_closedBall (0 : ℝ) 1).prod
      (isCompact_closedBall (0 : Fin (freeDimension a s p) → ℝ) R)) Q
  refine ⟨max 1 ((Q.factorial : ℝ)*C),le_max_left _ _,?_⟩
  intro f hf t ht j hj hjQ
  let g := fun z : ℝ => (z,D.basis.equivFun f)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_id.prodMk contDiff_const
  have hpoint : g t ∈ closedBall (0 : ℝ) 1 ×ˢ
      closedBall (0 : Fin (freeDimension a s p) → ℝ) R := by
    constructor
    · simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using ht
    · simpa only [mem_closedBall_zero_iff] using hf
  have he := norm_positive_composition_jet_at_le hj
    (hJ.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp)) hC.le le_rfl
    (fun k _ hk => hjets k (hk.trans hjQ) (g t) hpoint)
    (fun k hk _ => by
      obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
      apply norm_fixed_state_parameter_jet_le contDiffAt_id (D.basis.equivFun f) (by omega)
        zero_le_one
      rw [Nat.add_comm 1 l]
      exact G1.norm_iteratedFDeriv_id_le l t)
  have hfun : J ∘ g = dilatedInputCoordinates D f := by
    funext z
    rfl
  rw [hfun] at he
  have he' : ‖iteratedFDeriv ℝ j (dilatedInputCoordinates D f) t‖ ≤
      (j.factorial : ℝ)*C := by
    simpa only [one_pow,mul_one] using he
  apply he'.trans
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hjQ) hC.le).trans
    (le_max_right _ _)
end RothschildStein.G3

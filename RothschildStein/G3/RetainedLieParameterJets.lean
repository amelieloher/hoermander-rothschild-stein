-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLieAbsoluteLists
public import RothschildStein.G3.PositiveCompositionAt
public import RothschildStein.G3.FixedStateInputJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Fixing the initial spatial point gives a numerical scalar-parameter budget. -/
theorem norm_retainedLiePointList_parameter_jet_le {a s N Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (fs : List (formalSpan a s p)) (t : ℝ) (x : Fin N → ℝ)
    {B : ℝ} (hB : 1 ≤ B)
    (h : ChronologicalJetBounds Q B (fs.map (retainedLieAbsoluteStateMap D Φ)) (t,x))
    (j : ℕ) (hj : 1 ≤ j) (hjQ : j ≤ Q) :
    ‖iteratedFDeriv ℝ j (fun v => runRetainedLiePointList D Φ fs v x) t‖ ≤
      (Q.factorial : ℝ)*chronologicalJetBudget Q B fs.length := by
  let F := fun w : ℝ × (Fin N → ℝ) => runRetainedLiePointList D Φ fs w.1 w.2
  let g := fun v : ℝ => (v,x)
  have hF : ContDiffAt ℝ Q F (t,x) := by
    have he : F = Prod.snd ∘ chronologicalComposition
        (fs.map (retainedLieAbsoluteStateMap D Φ)) := by
      funext w
      exact congrArg Prod.snd (chronological_retainedLieAbsoluteStateMap D Φ fs w.1 w.2).symm
    rw [he]
    exact contDiffAt_snd.comp (t,x)
      (chronologicalComposition_contDiffAt_of_bounds Q B _ (t,x) h)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_id.prodMk contDiff_const
  have hM : 0 ≤ chronologicalJetBudget Q B fs.length :=
    zero_le_one.trans (chronologicalJetBudget_one_le Q B fs.length)
  have he := norm_positive_composition_jet_at_le (f := F) (g := g) (x := t) hj
    (hF.of_le (by exact_mod_cast hjQ)) (hg.contDiffAt.of_le (by simp)) hM le_rfl
    (fun k hk hkj => norm_retainedLiePointList_joint_jet_le D Φ fs (t,x) hB h k hk (hkj.trans hjQ))
    (fun k hk _ => by
      obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
      apply norm_fixed_state_parameter_jet_le contDiffAt_id x (by omega) zero_le_one
      rw [Nat.add_comm 1 l]
      exact G1.norm_iteratedFDeriv_id_le l t)
  have hfun : F ∘ g = (fun v => runRetainedLiePointList D Φ fs v x) := rfl
  rw [hfun,one_pow,mul_one] at he
  exact he.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hjQ) hM)
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FirstHolderNormFormula
public import RothschildStein.S.IntrinsicUniqueness
public import RothschildStein.S.HolderBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators ENNReal
namespace RothschildStein.H3

/-- On an open cutoff plateau, the exact fixed first-order
norm of the original input is bounded by the global compact product
norm. Integral curves are restricted using openness of the plateau. -/
theorem cutoff_plateau_first_holderNorm_le {N q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (α : ℝ)
    (u φ : (Fin N → ℝ) → ℝ) (jet : Fin q → (Fin N → ℝ) → ℝ)
    (hφ : EqOn φ 1 (U : Set (Fin N → ℝ)))
    (hi : ∀ i, hasIntrinsicWordDeriv X ⊤ [i.succ] (fun x => u x * φ x) (jet i)) :
    holderXENorm driftWeight X d U 1 α u ≤
      holderXENorm driftWeight X d ⊤ 1 α (fun x => u x * φ x) := by
  have he : EqOn (fun x => u x * φ x) u (U : Set (Fin N → ℝ)) := by
    intro x hx
    simp only [hφ hx, Pi.one_apply, mul_one]
  have hlocal (i : Fin q) : hasIntrinsicWordDeriv X U [i.succ] u (jet i) := by
    obtain ⟨a, ha, hd⟩ := hi i
    have hglobal : hasIntrinsicDeriv ⊤ (X i.succ) (fun x => u x * φ x) (jet i) :=
      S.hasIntrinsicDeriv_congr_input ⊤ (X i.succ) ha hd
    have hr : hasIntrinsicDeriv U (X i.succ) (fun x => u x * φ x) (jet i) := by
      intro x hx
      obtain ⟨⟨γ, h0, hγ, _⟩, hall⟩ := hglobal x (mem_univ x)
      refine ⟨⟨γ, h0, hγ, ?_⟩, fun γ' h0' hγ' _ =>
        hall γ' h0' hγ' (Eventually.of_forall fun _ => mem_univ _)⟩
      exact hγ.self_of_nhds.continuousAt.eventually_mem
        (U.isOpen.mem_nhds (by rw [h0]; exact hx))
    exact ⟨u, (fun _ _ => rfl), S.hasIntrinsicDeriv_congr_input U (X i.succ) he hr⟩
  rw [holderXENorm_drift_one_eq X d U α u jet hlocal,
    holderXENorm_drift_one_eq X d ⊤ α (fun x => u x * φ x) jet hi]
  apply add_le_add
  · rw [← S.holderENorm_congr d α (U : Set (Fin N → ℝ)) (fun x => u x * φ x) he]
    exact S.holderENorm_mono d α (⊤ : Opens (Fin N → ℝ))
      (fun x => u x * φ x) (subset_univ _)
  · exact Finset.sum_le_sum fun i _ =>
      S.holderENorm_mono d α (⊤ : Opens (Fin N → ℝ)) (jet i) (subset_univ _)

end RothschildStein.H3

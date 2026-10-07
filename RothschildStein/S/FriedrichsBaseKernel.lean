-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FriedrichsKernelDefs
public import RothschildStein.S.MollifierSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The fixed base kernel J(y) has uniformly bounded joint jets,
independently of x and ε (BB pp. 75–76). -/
theorem euclideanJ_joint_jetBound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
      ‖iteratedFDeriv ℝ m (fun p => euclideanJ n p.2) p‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := (euclideanJ_smooth_compact n).2.exists_bound_iteratedFDeriv
    (euclideanJ_smooth_compact n).1 m
  refine ⟨C,hC,?_⟩
  intro p
  let L := ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)
  change ‖iteratedFDeriv ℝ m (euclideanJ n ∘ L) p‖ ≤ C
  rw [L.iteratedFDeriv_comp_right (euclideanJ_smooth_compact n).1 p (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (euclideanJ n) (L p)‖ * ∏ _ : Fin m, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * 1 := by
      apply mul_le_mul (hb m le_rfl _) _ (by positivity) hC
      calc
        (∏ _ : Fin m, ‖L‖) ≤ ∏ _ : Fin m, (1 : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ =>
            ContinuousLinearMap.norm_snd_le ..)
        _ = 1 := by simp
    _ = C := mul_one C

/-- The base mollifier family belongs to the bounded kernel
class (BB (2.8), properties (a),(b), pp. 75–76). -/
def baseFriedrichsKernel (U : Set (Fin n → ℝ)) (δ : ℝ) :
    BoundedFriedrichsKernel U δ where
  toFun := fun _ _ y => euclideanJ n y
  smooth := fun _ _ => ((euclideanJ_smooth_compact n).1.comp contDiff_snd).contDiffOn
  support := by
    intro ε hε x hx y hy
    change ‖y-0‖ ≤ 1
    rw [sub_zero]
    by_contra hn
    exact hy (euclideanJ_vanish y (le_trans (by norm_num) (le_of_not_ge hn)))
  jetBound := by
    intro m
    obtain ⟨C,hC,hb⟩ := euclideanJ_joint_jetBound (n := n) m
    exact ⟨C,hC,fun _ _ p _ => hb p⟩

/-- Applying the base kernel is exactly ordinary mollification,
with the even-kernel identity (BB (2.6)–(2.8), p. 75). -/
theorem baseFriedrichsKernel_op (hn : 0 < n) (U : Set (Fin n → ℝ)) (δ : ℝ)
    (f : (Fin n → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    friedrichsKernelOp (baseFriedrichsKernel U δ).toFun f ε =
      euclideanRegularize n f ε := by
  funext x
  exact (euclideanRegularize_eq_integral_add hn f hε x).symm

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Function
open scoped BigOperators Topology ContDiff
namespace RothschildStein.S
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Fixing a scalar parameter cannot enlarge a joint jet norm
(BB p. 76; preferred joint-parameter encoding). -/
theorem norm_iteratedFDeriv_parameterSlice_le {f : P × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) (ε : ℝ) (x : P) :
    ‖iteratedFDeriv ℝ m (fun x => f (x,ε)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (x,ε)‖ := by
  let L : P →L[ℝ] P × ℝ := (ContinuousLinearMap.id ℝ P).prod 0
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun x => by
    change ‖(x,(0 : ℝ))‖ ≤ 1*‖x‖
    simp only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg x),one_mul,le_refl])
  let g : P × ℝ → ℝ := fun z => f (z+(0,ε))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun x => f (x,ε)) = g ∘ L := by
    funext x
    simp [g,L]
  rw [he,L.iteratedFDeriv_comp_right hg x (by simp)]
  have hj : iteratedFDeriv ℝ m g (L x) = iteratedFDeriv ℝ m f (x,ε) := by
    rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) m (0,ε)]
    simp [L]
  rw [hj]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f (x,ε)‖ * ∏ _ : Fin m, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ m f (x,ε)‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ∏ _ : Fin m, (1 : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)
        _ = 1 := by simp
    _ = _ := mul_one _

/-- Joint smoothness on a compact parameter rectangle gives
uniform finite-order slice jets, including ε approaching zero
(BB p. 76; preferred joint-parameter encoding). -/
theorem exists_parameterSlice_jetBound {f : P × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : Set P} (hK : IsCompact K)
    (a b : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc a b, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun x => f (x,ε)) x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (by simp)).continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro ε hε x hx
  exact (norm_iteratedFDeriv_parameterSlice_le hf m ε x).trans
    ((hC (x,ε) ⟨hx,hε⟩).trans (le_max_right _ _))

end RothschildStein.S

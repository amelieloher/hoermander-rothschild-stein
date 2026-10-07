-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Coordinate-direction bounds control the ambient multilinear operator norm. -/
theorem norm_multilinear_le_coordinate_budget {N k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin N → ℝ) F)
    {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ f : Fin k → Fin N, ‖T (fun i => Pi.single (f i) (1 : ℝ))‖ ≤ B) :
    ‖T‖ ≤ (N : ℝ)^k*B := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro m
  have hm : m = fun i => ∑ j : Fin N, m i j • Pi.single j (1 : ℝ) := by
    funext i j
    simp [Pi.single_apply,Pi.smul_apply]
  have he : T m = ∑ f : Fin k → Fin N, (∏ i : Fin k, m i (f i)) •
      T (fun i => Pi.single (f i) (1 : ℝ)) := by
    calc
      T m = T (fun i => ∑ j : Fin N, m i j • Pi.single j (1 : ℝ)) := congrArg T hm
      _ = _ := by
        change T.toMultilinearMap (fun i => ∑ j : Fin N, m i j • Pi.single j (1 : ℝ)) = _
        rw [T.toMultilinearMap.map_sum]
        apply Finset.sum_congr rfl
        intro f _
        exact T.toMultilinearMap.map_smul_univ (fun i => m i (f i)) (fun i => Pi.single (f i) (1 : ℝ))
  rw [he]
  apply (norm_sum_le _ _).trans
  have hterm (f : Fin k → Fin N) :
      ‖(∏ i : Fin k, m i (f i)) • T (fun i => Pi.single (f i) (1 : ℝ))‖ ≤
        (∏ i : Fin k, ‖m i‖)*B := by
    rw [norm_smul,norm_prod]
    apply mul_le_mul
    · exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_le_pi_norm (m i) (f i))
    · exact hcoord f
    · exact norm_nonneg _
    · exact Finset.prod_nonneg (fun i _ => norm_nonneg _)
  calc
    ∑ f : Fin k → Fin N, ‖(∏ i : Fin k, m i (f i)) • T (fun i => Pi.single (f i) (1 : ℝ))‖ ≤
        ∑ _f : Fin k → Fin N, (∏ i : Fin k, ‖m i‖)*B := Finset.sum_le_sum (fun f _ => hterm f)
    _ = (N : ℝ)^k*B*(∏ i : Fin k, ‖m i‖) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_pow]
      ring
end RothschildStein.G3

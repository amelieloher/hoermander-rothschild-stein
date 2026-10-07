-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteTopology
public import RothschildStein.G3.BCH
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Powers in the finite associative coefficient algebra are smooth
(BB p. 528). -/
theorem contDiff_finite_pow {a s : ℕ} {p : Fin a → ℕ+} (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun f : FiniteWordAlgebra a s p => f ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (contDiff_const (c := (1 : FiniteWordAlgebra a s p)))
  | succ n ih =>
    have h := (finiteMulCL.contDiff.comp ih).clm_apply (contDiff_id (E := FiniteWordAlgebra a s p) (𝕜 := ℝ))
    simpa only [Function.comp_apply, id_eq, finiteMulCL_apply, pow_succ] using h

/-- The finite exponential is smooth (BB p. 528). -/
theorem contDiff_finiteExp {a s : ℕ} {p : Fin a → ℕ+} :
    ContDiff ℝ (⊤ : ℕ∞) (finiteExp (a := a) (s := s) (p := p)) := by
  unfold finiteExp
  exact ContDiff.sum fun n _ => (contDiff_finite_pow n).const_smul _

/-- Finite logarithm correction is smooth on the entire associative
coefficient space (BB p. 528). -/
theorem contDiff_logApprox {a s : ℕ} {p : Fin a → ℕ+} (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun f : FiniteWordAlgebra a s p => logApprox f n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih =>
    exact ih.add ((contDiff_const.add contDiff_id).sub (contDiff_finiteExp.comp ih))

/-- Powers of degree at least two have zero differential at the origin
(BB pp. 530–531; polynomial origin calculation). -/
theorem hasFDerivAt_finite_pow_zero {a s : ℕ} {p : Fin a → ℕ+}
    (n : ℕ) (hn : 2 ≤ n) :
    HasFDerivAt (𝕜 := ℝ) (fun f : FiniteWordAlgebra a s p => f ^ n) 0 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hm : m ≠ 0 := by omega
  have hp := ((contDiff_finite_pow (a := a) (s := s) (p := p) m).differentiable (by simp)).differentiableAt (x := (0 : FiniteWordAlgebra a s p)) |>.hasFDerivAt
  have h := finiteMulCL.hasFDerivAt_of_bilinear hp (hasFDerivAt_id (0 : FiniteWordAlgebra a s p))
  convert h using 1
  · funext f
    exact pow_succ f m
  · ext v
    simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, zero_pow hm]

/-- The finite exponential has differential the identity at zero
(BB pp. 530–531; polynomial origin calculation). -/
theorem hasFDerivAt_finiteExp_zero {a s : ℕ} {p : Fin a → ℕ+} :
    HasFDerivAt (finiteExp (a := a) (s := s) (p := p)) (ContinuousLinearMap.id ℝ _) 0 := by
  have ht : HasFDerivAt (𝕜 := ℝ) (expTail (a := a) (s := s) (p := p)) 0 0 := by
    have h := HasFDerivAt.sum (u := Finset.range s) (fun n _ =>
      (hasFDerivAt_finite_pow_zero (a := a) (s := s) (p := p) (n + 2) (by omega)).const_smul
        (((n + 2).factorial : ℝ)⁻¹))
    convert h using 1
    · funext f
      simp only [expTail, Finset.sum_apply, Pi.smul_apply]
    · simp only [smul_zero, Finset.sum_const_zero]
  have he : finiteExp (a := a) (s := s) (p := p) = fun f => 1 + f + expTail f :=
    funext finiteExp_eq
  rw [he]
  convert ((hasFDerivAt_const (1 : FiniteWordAlgebra a s p) 0).add (hasFDerivAt_id 0)).add ht using 1
  all_goals first | rfl | simp

/-- The polynomial logarithm is inverse to exponentiation on the positive
Lie carrier (BB Proposition 9.72, pp. 475–476). -/
theorem logApprox_finiteExp {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) :
    logApprox (finiteExp f - 1) s = f := by
  have hv := finiteExp_sub_one_order hf
  apply finiteExp_injective_positive (logApprox_order hv s).1 hf
  rw [finiteExp_logApprox hv]
  abel
end RothschildStein.G3

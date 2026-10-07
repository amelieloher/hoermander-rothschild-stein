-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Defs
public import Hormander.A.SobolevScale
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

noncomputable section

namespace Hormander.B

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- The shared B multiplier is exactly A's Bessel multiplier. -/
theorem lambdaOperator_eq_Lambda {N : ℕ} (s : ℝ) :
    lambdaOperator (N := N) s = (Hormander.A.Lambda s).toLinearMap := rfl

/-- The shared B norm is the norm of A's bundled Sobolev representative. -/
theorem sobolevNorm_eq_schwartzToSobolev_norm {N : ℕ} (s : ℝ) (u : TestFunction N) :
    sobolevNorm s u = ‖Hormander.A.schwartzToSobolev s u‖ := rfl

/-- Transfer A's Fourier Sobolev norm identity to the shared B norm. -/
theorem sobolevNorm_eq_schwartzSobolevNorm {N : ℕ} (s : ℝ) (u : TestFunction N) :
    sobolevNorm s u = Hormander.A.schwartzSobolevNorm s u := by
  rw [sobolevNorm_eq_schwartzToSobolev_norm,
    Hormander.A.schwartzSobolevNorm_eq_schwartzToSobolev_norm]

theorem sobolevNorm_nonneg {N : ℕ} (s : ℝ) (u : TestFunction N) :
    0 ≤ sobolevNorm s u := norm_nonneg _

@[simp] theorem sobolevNorm_zero {N : ℕ} (s : ℝ) :
    sobolevNorm s (0 : TestFunction N) = 0 := by
  rw [sobolevNorm_eq_schwartzSobolevNorm]
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 _ (Hormander.A.Lambda s 0)‖ = 0
  rw [map_zero, map_zero, norm_zero]

theorem sobolevNorm_add_le {N : ℕ} (s : ℝ) (u v : TestFunction N) :
    sobolevNorm s (u + v) ≤ sobolevNorm s u + sobolevNorm s v := by
  simp only [sobolevNorm_eq_schwartzSobolevNorm, Hormander.A.schwartzSobolevNorm]
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 _ (Hormander.A.Lambda s (u + v))‖ ≤ _
  rw [map_add, map_add]
  exact norm_add_le _ _

theorem sobolevNorm_smul {N : ℕ} (s : ℝ) (c : ℂ) (u : TestFunction N) :
    sobolevNorm s (c • u) = ‖c‖ * sobolevNorm s u := by
  simp only [sobolevNorm_eq_schwartzSobolevNorm, Hormander.A.schwartzSobolevNorm]
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 _ (Hormander.A.Lambda s (c • u))‖ = _
  rw [map_smul, map_smul, norm_smul]
  rfl

/-- Bessel multipliers shift the Sobolev norm isometrically. -/
theorem sobolevNorm_lambdaOperator {N : ℕ} (s t : ℝ) (u : TestFunction N) :
    sobolevNorm t (lambdaOperator s u) = sobolevNorm (t + s) u := by
  simp only [sobolevNorm_eq_schwartzSobolevNorm, lambdaOperator_eq_Lambda,
    ContinuousLinearMap.coe_coe]
  simpa [add_comm] using Hormander.A.Lambda_sobolevNorm s t u

@[simp] theorem lambdaOperator_zero {N : ℕ} :
    lambdaOperator (N := N) 0 = LinearMap.id := by
  simp [lambdaOperator, SchwartzMap.fourierMultiplierCLM_const]

theorem lambdaOperator_comp {N : ℕ} (s t : ℝ) :
    (lambdaOperator (N := N) s).comp (lambdaOperator t) = lambdaOperator (s + t) := by
  apply LinearMap.ext
  intro u
  exact congrArg (fun L : TestFunction N →L[ℂ] TestFunction N => L u)
    (Hormander.A.Lambda_comp (N := N) s t)

@[simp] theorem sobolevNorm_zero_order {N : ℕ} (u : TestFunction N) :
    sobolevNorm 0 u = ‖u.toLp 2‖ := by
  rw [sobolevNorm_eq_schwartzSobolevNorm]
  have hzero : Hormander.A.Lambda 0 u = u := by
    change lambdaOperator 0 u = u
    simp
  simp only [Hormander.A.schwartzSobolevNorm, hzero]

/-- Composition adds operator orders. -/
theorem HasOrder.comp {N : ℕ} {m n : ℝ} {T U : Operator N}
    (hT : HasOrder m T) (hU : HasOrder n U) : HasOrder (m + n) (T.comp U) := by
  intro s
  obtain ⟨C, hC⟩ := hT s
  obtain ⟨D, hD⟩ := hU (s + m)
  refine ⟨C * D, fun u => ?_⟩
  calc
    sobolevNorm s (T.comp U u) ≤ (C : ℝ) * sobolevNorm (s + m) (U u) := hC _
    _ ≤ (C : ℝ) * ((D : ℝ) * sobolevNorm (s + m + n) u) :=
      mul_le_mul_of_nonneg_left (hD u) C.property
    _ = ((C * D : NNReal) : ℝ) * sobolevNorm (s + (m + n)) u := by
      simp only [NNReal.coe_mul, add_assoc, mul_assoc]

/-- Addition preserves a common operator order. -/
theorem HasOrder.add {N : ℕ} {m : ℝ} {T U : Operator N}
    (hT : HasOrder m T) (hU : HasOrder m U) : HasOrder m (T + U) := by
  intro s
  obtain ⟨C, hC⟩ := hT s
  obtain ⟨D, hD⟩ := hU s
  refine ⟨C + D, fun u => ?_⟩
  calc
    sobolevNorm s ((T + U) u) ≤ sobolevNorm s (T u) + sobolevNorm s (U u) :=
      sobolevNorm_add_le s _ _
    _ ≤ (C : ℝ) * sobolevNorm (s + m) u + (D : ℝ) * sobolevNorm (s + m) u :=
      add_le_add (hC u) (hD u)
    _ = ((C + D : NNReal) : ℝ) * sobolevNorm (s + m) u := by
      simp only [NNReal.coe_add]
      ring

/-- Scalar multiplication preserves the operator order. -/
theorem HasOrder.smul {N : ℕ} {m : ℝ} {T : Operator N}
    (hT : HasOrder m T) (c : ℂ) : HasOrder m (c • T) := by
  intro s
  obtain ⟨C, hC⟩ := hT s
  refine ⟨‖c‖₊ * C, fun u => ?_⟩
  change sobolevNorm s (c • T u) ≤ _
  rw [sobolevNorm_smul]
  calc
    ‖c‖ * sobolevNorm s (T u) ≤ ‖c‖ * ((C : ℝ) * sobolevNorm (s + m) u) :=
      mul_le_mul_of_nonneg_left (hC u) (norm_nonneg c)
    _ = ((‖c‖₊ * C : NNReal) : ℝ) * sobolevNorm (s + m) u := by
      simp only [NNReal.coe_mul, coe_nnnorm, mul_assoc]

/-- The zero operator has every order. -/
theorem hasOrder_zero {N : ℕ} (m : ℝ) : HasOrder m (0 : Operator N) := by
  intro s
  exact ⟨0, by simp⟩

/-- A Bessel multiplier has its displayed order, with constant one. -/
theorem hasOrder_lambdaOperator {N : ℕ} (m : ℝ) :
    HasOrder m (lambdaOperator (N := N) m) := by
  intro s
  refine ⟨1, fun u => ?_⟩
  simp [sobolevNorm_lambdaOperator]

end Hormander.B

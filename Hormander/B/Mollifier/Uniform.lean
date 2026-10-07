-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.DiffOps
public import Hormander.B.Fractional.Commutators

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Hormander.B

variable {N : ℕ} {ι : Type*}

/-- A family of operators has order `m` with a constant independent of the index. -/
def UniformOrder (m : ℝ) (T : ι → Operator N) : Prop :=
  ∀ s : ℝ, ∃ C : NNReal, ∀ (i : ι) (u : TestFunction N),
    sobolevNorm s (T i u) ≤ (C : ℝ) * sobolevNorm (s + m) u

theorem UniformOrder.add {m : ℝ} {T U : ι → Operator N} (hT : UniformOrder m T)
    (hU : UniformOrder m U) : UniformOrder m (fun i => T i + U i) := by
  intro s
  obtain ⟨C, hC⟩ := hT s
  obtain ⟨D, hD⟩ := hU s
  refine ⟨C + D, fun i u => ?_⟩
  calc sobolevNorm s ((T i + U i) u) ≤ sobolevNorm s (T i u) + sobolevNorm s (U i u) :=
        sobolevNorm_add_le s _ _
    _ ≤ (C : ℝ) * sobolevNorm (s + m) u + (D : ℝ) * sobolevNorm (s + m) u :=
        add_le_add (hC i u) (hD i u)
    _ = _ := by simp only [NNReal.coe_add]; ring

theorem UniformOrder.smul {m : ℝ} {T : ι → Operator N} (hT : UniformOrder m T) (c : ℂ) :
    UniformOrder m (fun i => c • T i) := by
  intro s
  obtain ⟨C, hC⟩ := hT s
  refine ⟨‖c‖₊ * C, fun i u => ?_⟩
  change sobolevNorm s (c • T i u) ≤ _
  rw [sobolevNorm_smul]
  calc ‖c‖ * sobolevNorm s (T i u) ≤ ‖c‖ * ((C : ℝ) * sobolevNorm (s + m) u) :=
        mul_le_mul_of_nonneg_left (hC i u) (norm_nonneg c)
    _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm, mul_assoc]

theorem uniformOrder_zero (m : ℝ) : UniformOrder m (fun _ : ι => (0 : Operator N)) :=
  fun s => ⟨0, fun i u => by simp⟩

theorem UniformOrder.sum {m : ℝ} {κ : Type*} (I : Finset κ) (T : κ → ι → Operator N)
    (h : ∀ k ∈ I, UniformOrder m (T k)) : UniformOrder m (fun i => ∑ k ∈ I, T k i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using uniformOrder_zero m
  | insert k I hk ih =>
    simp only [Finset.sum_insert hk]
    exact (h k (Finset.mem_insert_self _ _)).add
      (ih fun k' hk' => h k' (Finset.mem_insert_of_mem hk'))

theorem UniformOrder.comp_right {m n : ℝ} {T : ι → Operator N} (hT : UniformOrder m T)
    {U : Operator N} (hU : HasOrder n U) : UniformOrder (m + n) (fun i => (T i).comp U) := by
  intro s
  obtain ⟨C, hC⟩ := hT s
  obtain ⟨D, hD⟩ := hU (s + m)
  refine ⟨C * D, fun i u => ?_⟩
  calc sobolevNorm s ((T i).comp U u) ≤ (C : ℝ) * sobolevNorm (s + m) (U u) := hC i _
    _ ≤ (C : ℝ) * ((D : ℝ) * sobolevNorm (s + m + n) u) :=
        mul_le_mul_of_nonneg_left (hD u) C.property
    _ = _ := by simp only [NNReal.coe_mul, add_assoc, mul_assoc]

theorem UniformOrder.comp_left {m n : ℝ} {T : ι → Operator N} (hT : UniformOrder m T)
    {U : Operator N} (hU : HasOrder n U) : UniformOrder (n + m) (fun i => U.comp (T i)) := by
  intro s
  obtain ⟨C, hC⟩ := hU s
  obtain ⟨D, hD⟩ := hT (s + n)
  refine ⟨C * D, fun i u => ?_⟩
  calc sobolevNorm s (U.comp (T i) u) ≤ (C : ℝ) * sobolevNorm (s + n) (T i u) := hC _
    _ ≤ (C : ℝ) * ((D : ℝ) * sobolevNorm (s + n + m) u) :=
        mul_le_mul_of_nonneg_left (hD i u) C.property
    _ = _ := by simp only [NNReal.coe_mul, add_assoc, mul_assoc]

theorem HasOrder.uniform {m : ℝ} {T : Operator N} (h : HasOrder m T) :
    UniformOrder m (fun _ : ι => T) := fun s => by
  obtain ⟨C, hC⟩ := h s
  exact ⟨C, fun _ u => hC u⟩

/-- Family version of the single-kernel criterion. -/
theorem uniformOrder_of_kernelBound (T : ι → Operator N) (m : ℝ)
    (H : ∀ s : ℝ, ∃ k : Carrier N → ℝ≥0∞, Measurable k ∧ ∫⁻ a, k a ≠ ⊤ ∧
      ∀ (i : ι) (u : TestFunction N) (ξ : Carrier N),
        fourierWeightENN s (T i u) ξ ≤ ∫⁻ a, k a * fourierWeightENN (s + m) u (ξ - a)) :
    UniformOrder m T := by
  intro s
  obtain ⟨k, hk, hK, hb⟩ := H s
  refine ⟨(∫⁻ a, k a).toNNReal, fun i u => ?_⟩
  have := young_dominated k _ _ hk (measurable_fourierWeightENN (s + m) u) hK (hb i u)
  simpa [ENNReal.coe_toNNReal_eq_toReal] using ofReal_sobolevNorm_le_of_sq hK this

/-- Family version of the two-fold kernel criterion. -/
theorem uniformOrder_of_kernelBound₂ (T : ι → Operator N) (m : ℝ)
    (H : ∀ s : ℝ, ∃ k₁ k₂ : Carrier N → ℝ≥0∞, Measurable k₁ ∧ Measurable k₂ ∧
      ∫⁻ a, k₁ a ≠ ⊤ ∧ ∫⁻ a, k₂ a ≠ ⊤ ∧
      ∀ (i : ι) (u : TestFunction N) (ξ : Carrier N),
        fourierWeightENN s (T i u) ξ ≤
          ∫⁻ a, k₁ a * ∫⁻ b, k₂ b * fourierWeightENN (s + m) u (ξ - a - b)) :
    UniformOrder m T := by
  intro s
  obtain ⟨k₁, k₂, hk₁, hk₂, hK₁, hK₂, hb⟩ := H s
  refine ⟨((∫⁻ a, k₁ a) * (∫⁻ a, k₂ a)).toNNReal, fun i u => ?_⟩
  have hf := measurable_fourierWeightENN (s + m) u
  have h2 := young_lintegral_sq k₂ _ hk₂ hf hK₂
  have h2m := measurable_kernelConv k₂ _ hk₂ hf
  have h1 := young_dominated k₁ _ _ hk₁ h2m hK₁ (hb i u)
  have hKK : (∫⁻ a, k₁ a) * (∫⁻ a, k₂ a) ≠ ⊤ := ENNReal.mul_ne_top hK₁ hK₂
  have hmain : ∫⁻ ξ, fourierWeightENN s (T i u) ξ ^ 2 ≤
      ((∫⁻ a, k₁ a) * (∫⁻ a, k₂ a)) ^ 2 * ∫⁻ ξ, fourierWeightENN (s + m) u ξ ^ 2 := by
    calc _ ≤ _ := h1
      _ ≤ (∫⁻ a, k₁ a) ^ 2 * ((∫⁻ a, k₂ a) ^ 2 * ∫⁻ ξ, fourierWeightENN (s + m) u ξ ^ 2) := by
          gcongr
      _ = _ := by ring
  simpa [ENNReal.coe_toNNReal_eq_toReal] using ofReal_sobolevNorm_le_of_sq hKK hmain

end Hormander.B

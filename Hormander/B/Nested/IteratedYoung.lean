-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.SobolevFourier
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

noncomputable section

open MeasureTheory ENNReal
open scoped ENNReal

namespace Hormander.B

variable {N : ℕ}

/-- Iterated convolution of a list of kernels with a function. -/
def iterConv : List (Carrier N → ℝ≥0∞) → (Carrier N → ℝ≥0∞) → Carrier N → ℝ≥0∞
  | [], w => w
  | k :: ks, w => fun ξ => ∫⁻ a, k a * iterConv ks w (ξ - a)

theorem measurable_iterConv (ks : List (Carrier N → ℝ≥0∞)) (hks : ∀ k ∈ ks, Measurable k)
    {w : Carrier N → ℝ≥0∞} (hw : Measurable w) : Measurable (iterConv ks w) := by
  induction ks with
  | nil => exact hw
  | cons k ks ih =>
    exact measurable_kernelConv k _ (hks k (by simp)) (ih (fun k' hk' => hks k' (by simp [hk'])))

theorem list_prod_ne_top (l : List ℝ≥0∞) (h : ∀ x ∈ l, x ≠ ⊤) : l.prod ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons]
    exact ENNReal.mul_ne_top (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- Young's inequality for an iterated convolution. -/
theorem young_iterConv (ks : List (Carrier N → ℝ≥0∞)) (hks : ∀ k ∈ ks, Measurable k)
    (hfin : ∀ k ∈ ks, ∫⁻ a, k a ≠ ⊤) {w : Carrier N → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ ξ, iterConv ks w ξ ^ 2 ≤ (ks.map fun k => ∫⁻ a, k a).prod ^ 2 * ∫⁻ ξ, w ξ ^ 2 := by
  induction ks with
  | nil => simp [iterConv]
  | cons k ks ih =>
    have hk := hks k (by simp)
    have hkf := hfin k (by simp)
    have hks' : ∀ k' ∈ ks, Measurable k' := fun k' h => hks k' (by simp [h])
    have hfin' : ∀ k' ∈ ks, ∫⁻ a, k' a ≠ ⊤ := fun k' h => hfin k' (by simp [h])
    have h1 := young_lintegral_sq k (iterConv ks w) hk (measurable_iterConv ks hks' hw) hkf
    calc ∫⁻ ξ, iterConv (k :: ks) w ξ ^ 2 ≤ (∫⁻ a, k a) ^ 2 * ∫⁻ ξ, iterConv ks w ξ ^ 2 := h1
      _ ≤ (∫⁻ a, k a) ^ 2 * ((ks.map fun k => ∫⁻ a, k a).prod ^ 2 * ∫⁻ ξ, w ξ ^ 2) := by
          gcongr
          exact ih hks' hfin'
      _ = _ := by simp [List.map_cons, List.prod_cons]; ring

/-- An iterated-convolution bound on weighted Fourier transforms
gives an operator order. -/
theorem hasOrder_of_iterKernelBound (T : Operator N) (m : ℝ)
    (H : ∀ s : ℝ, ∃ (c : ℝ≥0∞) (ks : List (Carrier N → ℝ≥0∞)), c ≠ ⊤ ∧
      (∀ k ∈ ks, Measurable k) ∧ (∀ k ∈ ks, ∫⁻ a, k a ≠ ⊤) ∧
      ∀ (u : TestFunction N) (ξ : Carrier N),
        fourierWeightENN s (T u) ξ ≤ c * iterConv ks (fourierWeightENN (s + m) u) ξ) :
    HasOrder m T := by
  intro s
  obtain ⟨c, ks, hc, hks, hfin, hb⟩ := H s
  have hK : (c * (ks.map fun k => ∫⁻ a, k a).prod) ≠ ⊤ := by
    refine ENNReal.mul_ne_top hc ?_
    exact list_prod_ne_top (ks.map fun k => ∫⁻ a, k a) (by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact hfin k hk)
  refine ⟨((c * (ks.map fun k => ∫⁻ a, k a).prod).toNNReal), fun u => ?_⟩
  have hw := measurable_fourierWeightENN (s + m) u
  have hy := young_iterConv ks hks hfin hw
  have hmain : ∫⁻ ξ, fourierWeightENN s (T u) ξ ^ 2 ≤
      (c * (ks.map fun k => ∫⁻ a, k a).prod) ^ 2 * ∫⁻ ξ, fourierWeightENN (s + m) u ξ ^ 2 := by
    calc ∫⁻ ξ, fourierWeightENN s (T u) ξ ^ 2
        ≤ ∫⁻ ξ, (c * iterConv ks (fourierWeightENN (s + m) u) ξ) ^ 2 :=
          lintegral_mono fun ξ => pow_le_pow_left' (hb u ξ) 2
      _ = c ^ 2 * ∫⁻ ξ, iterConv ks (fourierWeightENN (s + m) u) ξ ^ 2 := by
          rw [← lintegral_const_mul' _ _ (pow_ne_top hc)]
          congr 1; funext ξ; ring
      _ ≤ c ^ 2 * ((ks.map fun k => ∫⁻ a, k a).prod ^ 2 * ∫⁻ ξ, fourierWeightENN (s + m) u ξ ^ 2) := by
          gcongr
      _ = _ := by ring
  simpa [ENNReal.coe_toNNReal_eq_toReal] using ofReal_sobolevNorm_le_of_sq hK hmain


theorem lintegral_pi_succ_cons {n : ℕ} (F : (Fin (n + 1) → Carrier N) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ a : Fin (n + 1) → Carrier N, F a = ∫⁻ b, ∫⁻ a, F (Fin.cons b a) := by
  have := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Carrier N) 0).symm
  rw [← this.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hc : ∀ a : Carrier N × (Fin n → Carrier N),
      ((⟨fun f => Fin.insertNth 0 f.1 f.2, fun f => (f 0, Fin.removeNth 0 f),
        fun _ => by simp, fun _ => by simp⟩ : Carrier N × (Fin n → Carrier N) ≃ (Fin (n + 1) → Carrier N)) a)
        = Fin.cons a.1 a.2 := fun a => by
    simp [Fin.insertNth_zero']
  simp only [hc]
  rw [Measure.volume_eq_prod]
  refine lintegral_prod _ ?_
  have hm : Measurable (fun p : Carrier N × (Fin n → Carrier N) =>
      (Fin.cons p.1 p.2 : Fin (n + 1) → Carrier N)) :=
    measurable_pi_iff.mpr (fun i => Fin.cases (by simpa using measurable_fst)
      (fun j => by
        simp only [Fin.cons_succ]
        exact (measurable_pi_apply j).comp measurable_snd) i)
  exact (hF.comp hm).aemeasurable


theorem lintegral_pi_zero (F : (Fin 0 → Carrier N) → ℝ≥0∞) :
    ∫⁻ a : Fin 0 → Carrier N, F a = F default := by
  have : (volume : Measure (Fin 0 → Carrier N)) = Measure.dirac default := by
    rw [volume_pi, Measure.pi_of_empty]
    congr 1
    exact Subsingleton.elim _ _
  rw [this, lintegral_dirac' _ (measurable_of_finite F)]

/-- The lower integral over the increments is the iterated convolution of the kernels. -/
theorem lintegral_pi_eq_iterConv (q : ℕ) :
    ∀ (ks : Fin q → Carrier N → ℝ≥0∞), (∀ i, Measurable (ks i)) →
      ∀ {w : Carrier N → ℝ≥0∞}, Measurable w → ∀ ξ : Carrier N,
        ∫⁻ a : Fin q → Carrier N, (∏ i, ks i (a i)) * w (ξ - ∑ i, a i) =
          iterConv (List.ofFn ks) w ξ := by
  induction q with
  | zero =>
    intro ks hks w hw ξ
    rw [lintegral_pi_zero]
    simp [iterConv]
  | succ q ih =>
    intro ks hks w hw ξ
    have hF : Measurable (fun a : Fin (q + 1) → Carrier N => (∏ i, ks i (a i)) * w (ξ - ∑ i, a i)) := by
      refine (Finset.measurable_prod _ (fun i _ => (hks i).comp (measurable_pi_apply i))).mul ?_
      exact hw.comp (measurable_const.sub (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)))
    rw [lintegral_pi_succ_cons _ hF, List.ofFn_succ]
    simp only [iterConv]
    refine lintegral_congr fun b => ?_
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hm : Measurable (fun a : Fin q → Carrier N =>
        (∏ i, ks i.succ (a i)) * w (ξ - b - ∑ i, a i)) := by
      refine (Finset.measurable_prod _ (fun i _ => (hks i.succ).comp (measurable_pi_apply i))).mul ?_
      exact hw.comp (measurable_const.sub (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)))
    have e : ∀ a : Fin q → Carrier N, ks 0 b * (∏ i, ks i.succ (a i)) * w (ξ - (b + ∑ i, a i)) =
        ks 0 b * ((∏ i, ks i.succ (a i)) * w (ξ - b - ∑ i, a i)) := by
      intro a; rw [← sub_sub, mul_assoc]
    simp_rw [e]
    rw [lintegral_const_mul _ hm]
    congr 1
    exact ih (fun i => ks i.succ) (fun i => hks i.succ) hw (ξ - b)

end Hormander.B

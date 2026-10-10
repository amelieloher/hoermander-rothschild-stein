-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.WeakCompactness
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.L2Space

/-! Almost-everywhere scalar bounds are retained by weak limits on finite measure spaces. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- A common almost-everywhere bound passes to a weak L² limit. -/
theorem ae_abs_le_of_tendsto_weak {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasure μ] {u : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} {C : ℝ}
    (hu : ∀ n, ∀ᵐ x ∂μ, |u n x| ≤ C)
    (hlim : Tendsto (fun n => toWeakSpace ℝ (Lp ℝ 2 μ) (u n)) atTop
      (𝓝 (toWeakSpace ℝ (Lp ℝ 2 μ) g))) : ∀ᵐ x ∂μ, |g x| ≤ C := by
  let c : Lp ℝ 2 μ := (memLp_const C).toLp (fun _ : A => C)
  have hc : c =ᵐ[μ] fun _ => C := (memLp_const C).coeFn_toLp
  have hmem : ∀ n, u n ∈ Icc (-c) c := by
    intro n
    constructor
    · apply (Lp.coeFn_le _ _).mp
      filter_upwards [hu n, hc, Lp.coeFn_neg c] with x hx hcx hncx
      simpa only [hncx, Pi.neg_apply, hcx] using (abs_le.mp hx).1

    · apply (Lp.coeFn_le _ _).mp
      filter_upwards [hu n, hc] with x hx hcx
      rw [hcx]
      exact (abs_le.mp hx).2
  let _ : PosSMulMono ℝ (Lp ℝ 2 μ) := ⟨by
    intro a ha v w hvw
    apply (Lp.coeFn_le _ _).mp
    have hvw' := (Lp.coeFn_le _ _).mpr hvw
    filter_upwards [hvw', Lp.coeFn_smul a v, Lp.coeFn_smul a w] with x hx hv hw
    simpa only [hv, hw, Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left hx ha⟩
  have hg := mem_of_tendsto_weak_of_convex (convex_Icc (-c) c) isClosed_Icc hmem hlim
  have hlow := (Lp.coeFn_le _ _).mpr hg.1
  have hhigh := (Lp.coeFn_le _ _).mpr hg.2
  filter_upwards [hlow, hhigh, hc, Lp.coeFn_neg c] with x hl hh hcx hncx
  simp only [hncx, Pi.neg_apply, hcx] at hl
  rw [hcx] at hh
  exact abs_le.mpr ⟨hl, hh⟩

/-- Uniformly bounded L² functions on a finite separable measure space have a weakly
convergent subsequence whose limit retains the same pointwise bound. -/
theorem exists_weak_subseq_of_ae_abs_le {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasure μ] [SecondCountableTopology (Lp ℝ 2 μ)]
    (u : ℕ → Lp ℝ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ n, ∀ᵐ x ∂μ, |u n x| ≤ C) :
    ∃ g : Lp ℝ 2 μ, (∀ᵐ x ∂μ, |g x| ≤ C) ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => toWeakSpace ℝ (Lp ℝ 2 μ) (u (σ n))) atTop
        (𝓝 (toWeakSpace ℝ (Lp ℝ 2 μ) g)) := by
  let c : Lp ℝ 2 μ := (memLp_const C).toLp (fun _ : A => C)
  have hc : c =ᵐ[μ] fun _ => C := (memLp_const C).coeFn_toLp
  have hb : ∀ n, ‖u n‖ ≤ ‖c‖ := by
    intro n
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hu n, hc] with x hx hcx
    simpa only [Real.norm_eq_abs, hcx, abs_of_nonneg hC] using hx
  obtain ⟨g, _, σ, hσ, hlim⟩ := exists_weakly_convergent_subseq u hb
  exact ⟨g, ae_abs_le_of_tendsto_weak (fun n => hu (σ n)) hlim, σ, hσ, hlim⟩

/-- Pairing limits against an arbitrary family of L² tests identify the same bounded
weak limit obtained from uniformly bounded approximants. -/
theorem exists_bounded_weak_limit_with_pairings {A I : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasure μ] [SecondCountableTopology (Lp ℝ 2 μ)]
    (u : ℕ → Lp ℝ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ n, ∀ᵐ x ∂μ, |u n x| ≤ C) (v : I → Lp ℝ 2 μ) (ℓ : I → ℝ)
    (hpair : ∀ i, Tendsto (fun n => inner ℝ (v i) (u n)) atTop (𝓝 (ℓ i))) :
    ∃ g : Lp ℝ 2 μ, (∀ᵐ x ∂μ, |g x| ≤ C) ∧ ∀ i, inner ℝ (v i) g = ℓ i := by
  obtain ⟨g, hg, σ, hσ, hlim⟩ := exists_weak_subseq_of_ae_abs_le u hC hu
  refine ⟨g, hg, fun i => ?_⟩
  exact tendsto_nhds_unique ((tendsto_weak_iff_inner.mp hlim) (v i))
    ((hpair i).comp hσ.tendsto_atTop)

end HeatKernel

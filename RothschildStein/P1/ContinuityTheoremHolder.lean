-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuitySingularTests
public import RothschildStein.P1.ContinuityReconstructionHolder
public import RothschildStein.P1.RestrictedErrorMeasurable

/-!
# Continuity: calculus of the Hölder norm and of `L^p` norms for the multiplier term

The multiplier `μ ∈ C_c^∞(V)` of a type-`0` operator acts by `f ↦ μ f`. This module collects
the elementary norm calculus used to assemble the continuity theorem:

* `holderENorm_zero`, `holderENorm_neg`, `holderENorm_add_le`: the Hölder norm of `0`, of a
  negative and of a sum (the subtractive form is `holderENorm_sub_le`);
* `LiftedChart.exists_holderENorm_mul_le`: for a smooth multiplier `b` with compact support in the
  open patch `V ⊆ U`, `‖b f‖_{C^α(V)} ≤ K ‖f‖_{C^α(V)}`, with `K` built from `sup |b|`, the Lipschitz
  constant of `b` for `d̃` and the margin of `supp b` in `V`: `[b f]_α ≤ ‖b‖_∞ [f]_α + [b]_α ‖f‖_∞`
  (it is the controlled extension of the input used in the reconstruction, read on `V`);
* `memLp_mul_of_bound`: multiplication by a bounded measurable function is bounded on `L^p`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace RothschildStein.P1

section HolderNorm

variable {n' : ℕ} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} {V : Set (Fin n' → ℝ)}

/-- The Hölder norm of the zero function is zero. -/
theorem holderENorm_zero : holderENorm d α V (fun _ => (0 : ℝ)) = 0 := by
  unfold holderENorm holderSeminorm
  have h1 : (⨆ x : V, ENNReal.ofReal |(0 : ℝ)|) = 0 := by simp
  have h2 : sInf {C : ℝ≥0∞ | C < ⊤ ∧ ∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ →
      ENNReal.ofReal |(0 : ℝ) - 0| ≤ C * (d x y) ^ α} = 0 := by
    refine le_antisymm (sInf_le ⟨by simp, fun x _ y _ _ => by simp⟩) bot_le
  rw [h1, h2, add_zero]

/-- The Hölder norm is invariant under negation. -/
theorem holderENorm_neg (f : (Fin n' → ℝ) → ℝ) :
    holderENorm d α V (fun x => -f x) = holderENorm d α V f := by
  unfold holderENorm holderSeminorm
  have h1 : (⨆ x : V, ENNReal.ofReal |-f x|) = ⨆ x : V, ENNReal.ofReal |f x| := by
    simp only [abs_neg]
  have h2 : ∀ x y : Fin n' → ℝ, |(-f x) - (-f y)| = |f x - f y| := fun x y => by
    rw [show (-f x) - (-f y) = -(f x - f y) by ring, abs_neg]
  simp only [h1, h2]

/-- The Hölder norm is subadditive (for sums). -/
theorem holderENorm_add_le (hα : 0 ≤ α) (f g : (Fin n' → ℝ) → ℝ) :
    holderENorm d α V (fun x => f x + g x) ≤ holderENorm d α V f + holderENorm d α V g := by
  have h := holderENorm_sub_le (d := d) (V := V) hα f (fun x => -g x)
  rw [holderENorm_neg] at h
  simpa only [sub_neg_eq_add] using h

end HolderNorm

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- **The multiplier term in `C^α`**: for a smooth `b` with compact support in the open patch
`V ⊆ U`, `‖b f‖_{C^α(V)} ≤ K ‖f‖_{C^α(V)}` for every `f`, `0 < α ≤ 1` (`holderENorm`, lifted
control distance). -/
theorem exists_holderENorm_mul_le {V : Set (Fin (n + m) → ℝ)} (hVo : IsOpen V) (hVU : V ⊆ C.U)
    {b : (Fin (n + m) → ℝ) → ℝ} (hbd : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b)
    (hbV : tsupport b ⊆ V) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ,
      holderENorm C.dl α V (fun x => b x * f x) ≤ ENNReal.ofReal K * holderENorm C.dl α V f := by
  obtain ⟨K, hK, hKb⟩ := exists_boundedHolder_mul_extension (C := C) hVo hVU hbd hbc hbV hα0 hα1
  exact ⟨K, hK, fun f => (holderENorm_le_boundedHolderNorm hVU hα0 _).trans (hKb f)⟩

end LiftedChart

/-- **The multiplier term in `L^p`**: multiplication by a bounded measurable function maps
`L^p(μ)` to itself with norm at most the sup bound. -/
theorem memLp_mul_of_bound {E : Type*} [MeasurableSpace E] {μ : Measure E} {p : ℝ≥0∞}
    {b f : E → ℝ} {M : ℝ} (hb : AEStronglyMeasurable b μ) (hM : ∀ x, |b x| ≤ M)
    (hf : MemLp f p μ) :
    MemLp (fun x => b x * f x) p μ ∧
      eLpNorm (fun x => b x * f x) p μ ≤ ENNReal.ofReal M * eLpNorm f p μ := by
  have hle : ∀ᵐ x ∂μ, ‖b x * f x‖ ≤ M * ‖f x‖ := Filter.Eventually.of_forall fun x => by
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)
  have hm : AEStronglyMeasurable (fun x => b x * f x) μ := hb.mul hf.aestronglyMeasurable
  exact ⟨hf.of_le_mul hm hle, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hle p⟩

end RothschildStein.P1

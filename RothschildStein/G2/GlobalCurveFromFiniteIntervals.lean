-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowUniqueness
public import Mathlib.Analysis.ODE.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.G2

/-- Uniqueness glues curves through one initial point on arbitrarily
long finite intervals into a genuine global integral curve. -/
theorem exists_global_integralCurve_of_finite_intervals {N : ℕ}
    (Z : (Fin N → ℝ) → (Fin N → ℝ)) (hZ : ContDiff ℝ (⊤ : ℕ∞) Z)
    (x : Fin N → ℝ)
    (hfinite : ∀ T : ℝ, 0 < T → ∃ γ : ℝ → (Fin N → ℝ), γ 0 = x ∧
      ∀ t ∈ Ioo (-T) T, HasDerivAt γ (Z (γ t)) t) :
    ∃ γ : ℝ → (Fin N → ℝ), γ 0 = x ∧ IsIntegralCurve γ (fun _ => Z) := by
  classical
  let R := {T : ℝ // 0 < T}
  have hex : ∀ T : R, ∃ γ : ℝ → (Fin N → ℝ), γ 0 = x ∧
      ∀ t ∈ Ioo (-T.val) T.val, HasDerivAt γ (Z (γ t)) t :=
    fun T => hfinite T.val T.property
  choose β hzero hder using hex
  let γ := fun t : ℝ => β ⟨|t|+1,by positivity⟩ t
  have heq : ∀ T : R, EqOn γ (β T) (Ioo (-T.val) T.val) := by
    intro T t ht
    let S : R := ⟨|t|+1,by positivity⟩
    let r := min S.val T.val
    have hr : 0 < r := lt_min S.property T.property
    have htS : t ∈ Ioo (-S.val) S.val := by
      dsimp [S]; constructor <;> linarith [le_abs_self t,neg_abs_le t]
    have htR : t ∈ Ioo (-r) r := by
      exact abs_lt.mp (lt_min (abs_lt.mpr htS) (abs_lt.mpr ht))
    have hsubS : Ioo (-r) r ⊆ Ioo (-S.val) S.val :=
      fun u hu => ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hu.1,
        hu.2.trans_le (min_le_left _ _)⟩
    have hsubT : Ioo (-r) r ⊆ Ioo (-T.val) T.val :=
      fun u hu => ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hu.1,
        hu.2.trans_le (min_le_right _ _)⟩
    exact G1.integralCurve_eqOn isOpen_univ hZ.contDiffOn
      (show (0 : ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
      (fun u hu => ⟨hder S u (hsubS hu),mem_univ _⟩)
      (fun u hu => ⟨hder T u (hsubT hu),mem_univ _⟩)
      ((hzero S).trans (hzero T).symm) htR
  refine ⟨γ,hzero ⟨|0|+1,by positivity⟩,?_⟩
  intro t
  let T : R := ⟨|t|+1,by positivity⟩
  have ht : t ∈ Ioo (-T.val) T.val := by
    dsimp [T]; constructor <;> linarith [le_abs_self t,neg_abs_le t]
  have hg : γ =ᶠ[𝓝 t] β T := Filter.Eventually.mono (isOpen_Ioo.mem_nhds ht) (fun u hu => heq T hu)
  have hh := (hder T t ht).congr_of_eventuallyEq hg
  rwa [← hg.self_of_nhds] at hh

end RothschildStein.G2

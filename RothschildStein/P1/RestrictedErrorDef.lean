-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorKernel
public import RothschildStein.P1.TypeKernel

/-!
# The restricted error of the right parametrix: definition and the small-ball setup

For a kernel `kk` on a lifted chart `C`, `U_r = B̃(ξ₀, r) = rsBall C.O w C.Xl ξ₀ r`, and the zero
extension `E_r f = 1_{U_r} f`, the **restricted error** is
`𝓕_r f = (∫ kk(·, η) E_r f(η) dη)|_{U_r}` (`LiftedChart.restrictedError`). On `U_r` it is the integral
over `U_r` of the cut kernel (`restrictedError_eq`), and for `0 < r < r_*` the abstract small-ball
hypotheses hold (`IsSmallBallRadius.exists_setup`), so the bounds of `RestrictedErrorLp` and
`RestrictedErrorBounds` apply (BB pp. 606–607).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The **restricted error** `𝓕_r f = (∫ kk(·, η) E_r f(η) dη)|_{U_r}` of a kernel `kk`
(the kernel of `F_R^chart`), with `U_r = B̃(ξ₀, r) = rsBall C.O w C.Xl ξ₀ r` and `E_r f = 1_{U_r} f`
the zero extension (BB pp. 606–607). The restriction to `U_r` is implicit:
`𝓕_r f` is only used on `U_r`. -/
def restrictedError (ξ₀ : Fin (n + m) → ℝ) (r : ℝ)
    (kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) (f : (Fin (n + m) → ℝ) → ℝ)
    (ξ : Fin (n + m) → ℝ) : ℝ :=
  ∫ η, kk ξ η * (rsBall C.O w C.Xl ξ₀ r).indicator f η

variable {C} {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar r : ℝ}
  {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {A B : ℝ}

/-- On `U_r` the restricted error is the integral over `U_r` of the
cut kernel (the diagonal is null). -/
theorem restrictedError_eq (hSm : MeasurableSet (rsBall C.O w C.Xl ξ₀ r))
    {f : (Fin (n + m) → ℝ) → ℝ} {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ rsBall C.O w C.Xl ξ₀ r)
    (hnull : volume ({ξ} : Set (Fin (n + m) → ℝ)) = 0) :
    C.restrictedError ξ₀ r kk f ξ =
      ∫ y in rsBall C.O w C.Xl ξ₀ r, sliceKernel (rsBall C.O w C.Xl ξ₀ r) kk ξ y * f y := by
  set S := rsBall C.O w C.Xl ξ₀ r with hS
  unfold restrictedError
  have e1 : (fun η => kk ξ η * S.indicator f η) = S.indicator (fun η => kk ξ η * f η) := by
    funext η
    exact (Set.indicator_mul_right S (fun η => kk ξ η) f).symm
  rw [e1, integral_indicator hSm]
  refine integral_congr_ae ?_
  have hne : ∀ᵐ η ∂(volume : Measure (Fin (n + m) → ℝ)), η ≠ ξ := by
    have := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [this] with η hη
    simpa using hη
  filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae hne] with η hη hηne
  rw [sliceKernel_of_mem hξ hη hηne.symm]

/-- **The small-ball setup**: for an admissible radius and kernel
hypotheses there is `Cv` such that for every `0 < r < r_*` the abstract `ShellData` on `U_r`, the
abstract `SliceBounds` of the cut kernel, and nullity of points hold. -/
theorem IsSmallBallRadius.exists_setup (hr : C.IsSmallBallRadius K₀ ξ₀ rstar)
    (hk : C.RestrictedKernelBounds K₀ kk A B) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ r : ℝ, 0 < r → r < rstar →
      ShellData volume (rsBall C.O w C.Xl ξ₀ r) (fun x y => (C.dl x y).toReal)
          (C.G.homogeneousDimension - 1) r Cv ∧
        SliceBounds (rsBall C.O w C.Xl ξ₀ r) (fun x y => (C.dl x y).toReal)
          (C.G.homogeneousDimension - 1) (sliceKernel (rsBall C.O w C.Xl ξ₀ r) kk) A B ∧
        ∀ ξ ∈ rsBall C.O w C.Xl ξ₀ r, volume ({ξ} : Set (Fin (n + m) → ℝ)) = 0 := by
  obtain ⟨Cv, hCv, hshell⟩ := hr.exists_shellData
  refine ⟨Cv, hCv, fun r hr0 hrr => ?_⟩
  have hS := hshell r hr0 hrr
  have hd2 : ∀ x ∈ rsBall C.O w C.Xl ξ₀ r, ∀ y ∈ rsBall C.O w C.Xl ξ₀ r, C.dl x y < 2 := by
    intro x hx y hy
    have := C.dl_lt_of_mem_rsBall hr0 hx hy
    refine lt_of_lt_of_le this ?_
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (by linarith [hr.le_one])
  refine ⟨hS, hk.sliceBounds (hr.ball_subset r hr0 hrr) hS.measurableSet (fun y hy => hy.1) hd2,
    fun ξ hξ => ?_⟩
  refine measure_mono_null (t := rsBall C.O w C.Xl ξ₀ r ∩
    {y | (fun x y => (C.dl x y).toReal) ξ y ≤ 0}) ?_ (hS.measure_pole_eq_zero hξ)
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact ⟨hξ, le_of_eq (hS.dr_self y hξ)⟩

end LiftedChart

end RothschildStein.P1

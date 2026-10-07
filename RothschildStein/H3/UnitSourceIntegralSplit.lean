-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.UnitSourceKernelSplit
public import RothschildStein.H3.TypeZeroTailYoung

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Positive truncations split into the radially truncated kernel integral
and one absolutely convergent tail, independent of the truncation scale. -/
theorem unit_source_truncated_integral_split (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {k u : (Fin N → ℝ) → ℝ}
    (hk : TypeZero G ν k) (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hsu : ∀ y, 1 ≤ ν y → u y = 0) {x : Fin N → ℝ} (hx : ν x < 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (∫ y in {y | ε < G2.gaugeDistance G ν x y}, u y * k (G.mul (G.inv y) x)) =
      (∫ y in {y | ε < G2.gaugeDistance G ν x y}, u y * truncatedKernel G ν k x y) +
        G2.groupConvolution G u (typeZeroUnitTail ν k) x := by
  let A : Set (Fin N → ℝ) := {y | ε < G2.gaugeDistance G ν x y}
  let f : (Fin N → ℝ) → ℝ := fun y => u y * k (G.mul (G.inv y) x)
  let g : (Fin N → ℝ) → ℝ := fun y => u y * typeZeroUnitTail ν k (G.mul (G.inv y) x)
  have hf : IntegrableOn f A volume := (hk.hasPrincipalValue G hu hs x).1 ε hε
  have hg : Integrable g volume := G2.groupConvolutionExistsAt_of_memLp_conjugate G
    (p := ∞) (q := 1) (hu.continuous.memLp_of_hasCompactSupport hs)
    (memLp_one_iff_integrable.mpr hk.unitTail_integrable_and_bound.1) x
  have he : (fun y => u y * truncatedKernel G ν k x y) = f - g := by
    funext y
    have h := unit_source_kernel_split G ν h1 hsym k u hsu hx y
    change u y * truncatedKernel G ν k x y =
      u y * k (G.mul (G.inv y) x) - u y * typeZeroUnitTail ν k (G.mul (G.inv y) x)
    linarith
  have hz : (∫ y in A, g y) = ∫ y, g y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hny : ν (G.mul (G.inv y) x) < 1 := by
      change ¬ ε < ν (G.mul (G.inv y) x) at hy
      exact (le_of_not_gt hy).trans_lt hε1
    dsimp only [g]
    rw [typeZeroUnitTail_eq_zero_of_lt_one ν k hny, mul_zero]
  rw [he]
  change (∫ y in A, f y) = (∫ y in A, f y - g y) + _
  rw [integral_sub hf hg.integrableOn, hz, G2.groupConvolution_eq_integral]
  change (∫ y in A, f y) = ((∫ y in A, f y) - ∫ y, g y) + ∫ y, g y
  ring


/-- The radially truncated kernel has the exact local limit obtained by
subtracting the absolutely convergent tail from the full principal value. -/
theorem unit_source_radial_truncation_limit (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {k u : (Fin N → ℝ) → ℝ}
    (hk : TypeZero G ν k) (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hsu : ∀ y, 1 ≤ ν y → u y = 0) {x : Fin N → ℝ} (hx : ν x < 1) :
    Tendsto (fun ε : ℝ => ∫ y in {y | ε < G2.gaugeDistance G ν x y},
      u y * truncatedKernel G ν k x y) (𝓝[>] 0)
      (𝓝 (H1.principalValueConvolution G ν k u x -
        G2.groupConvolution G u (typeZeroUnitTail ν k) x)) := by
  have hlim := (hk.hasPrincipalValue G hu hs x).2.sub
    (tendsto_const_nhds (x := G2.groupConvolution G u (typeZeroUnitTail ν k) x))
  apply hlim.congr'
  have hsmall0 : ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 :=
    Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hε1
  have he := unit_source_truncated_integral_split G ν h1 hsym hk hu hs hsu hx hε hε1
  change (∫ y in {y | ε < G2.gaugeDistance G ν x y},
      u y * k (G.mul (G.inv y) x)) - G2.groupConvolution G u (typeZeroUnitTail ν k) x = _
  linarith

end RothschildStein.H3

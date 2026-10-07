-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorShell
public import RothschildStein.P1.SchurLpNorm

/-!
# Restricted-error bounds: row/column integrals, sup bound and the `L^p` bound

The restricted error `𝓕_r f = (∫ k(·, η) E_r f(η) dη)|_{U_r}` only sees the kernel on `U_r × U_r`
off the diagonal. `sliceKernel S k` is the kernel cut to `S × S` minus the diagonal; a
`SliceBounds` structure records its size bound `|K x y| ≤ A / dr^q` (`q + 1 = Q`) and the
first-variable difference bound `|K x' y - K x y| ≤ B h / dr(x', y)^(q+1)` for
`2 h < dr(x', y)` (`h = dr x x'`), the difference estimates of the kernel estimates at `ℓ = 1`. Row and column
integrals over `S` are `O(ρ)` by dyadic shells (`ShellData.lintegral_row_le`), so Schur's lemma
(`integralOperator_schur_eLpNorm_bound`) gives `‖𝓕_r‖_{L^p → L^p} ≤ C ρ` with `C` independent
of `p`, and the sup bound `‖𝓕_r f‖_∞ ≤ C ρ ‖f‖_∞` (BB pp. 606–607).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RothschildStein.P1

variable {E : Type*} [MeasurableSpace E]

/-- The kernel `k` cut to `S × S` off the diagonal (the only part
of the kernel the restricted operator on `S` sees, up to a null set). -/
def sliceKernel (S : Set E) (k : E → E → ℝ) (x y : E) : ℝ :=
  ((S ×ˢ S) \ Set.diagonal E).indicator (fun z : E × E => k z.1 z.2) (x, y)

omit [MeasurableSpace E] in
theorem sliceKernel_of_mem {S : Set E} {k : E → E → ℝ} {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hne : x ≠ y) : sliceKernel S k x y = k x y :=
  Set.indicator_of_mem (s := (S ×ˢ S) \ Set.diagonal E) (f := fun z : E × E => k z.1 z.2)
    (show (x, y) ∈ (S ×ˢ S) \ Set.diagonal E from ⟨⟨hx, hy⟩, fun h => hne h⟩)

omit [MeasurableSpace E] in
theorem sliceKernel_of_not_mem {S : Set E} {k : E → E → ℝ} {x y : E}
    (h : x ∉ S ∨ y ∉ S ∨ x = y) : sliceKernel S k x y = 0 := by
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨⟨hx, hy⟩, hne⟩
  rcases h with h | h | h
  exacts [h hx, h hy, hne h]

/-- The difference-bound hypotheses of the small-ball estimates, for a
kernel `K` supported in `S × S`: measurability, the size bound `|K x y| ≤ A / dr^q` and the
first-variable difference bound `|K x' y - K x y| ≤ B h / dr(x', y)^(q+1)` for
`2 h < dr(x', y)`, `h = dr x x'` (`q + 1` is the homogeneous dimension). -/
structure SliceBounds (S : Set E) (dr : E → E → ℝ) (q : ℕ) (K : E → E → ℝ) (A B : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  B_nonneg : 0 ≤ B
  measurable : Measurable (Function.uncurry K)
  zero_left : ∀ x y, x ∉ S → K x y = 0
  zero_right : ∀ x y, y ∉ S → K x y = 0
  size : ∀ x ∈ S, ∀ y ∈ S, |K x y| ≤ A / dr x y ^ q
  diff : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ S, 2 * dr x x' < dr x' y →
    |K x' y - K x y| ≤ B * dr x x' / dr x' y ^ (q + 1)

/-- `|∫ g| ≤ ∫ |g|` in `ℝ≥0∞`, with no integrability hypothesis. -/
theorem ofReal_abs_integral_le (g : E → ℝ) (T : Measure E) :
    ENNReal.ofReal |∫ y, g y ∂T| ≤ ∫⁻ y, ‖g y‖ₑ ∂T := by
  have := enorm_integral_le_lintegral_enorm (μ := T) g
  rwa [Real.enorm_eq_ofReal_abs] at this

namespace SliceBounds

variable {μ : Measure E} {S : Set E} {dr : E → E → ℝ} {q : ℕ} {ρ Cv : ℝ} {K : E → E → ℝ}
  {A B : ℝ} (hS : ShellData μ S dr q ρ Cv) (hK : SliceBounds S dr q K A B) {x : E}

include hS hK

/-- The row size bound with a bounded input value. -/
theorem enorm_mul_le (hx : x ∈ S) {y : E} (hy : y ∈ S) {v M : ℝ} (hv : |v| ≤ M) :
    ‖K x y * v‖ₑ ≤ ENNReal.ofReal (A * M / dr x y ^ q) := by
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc |K x y| * |v| ≤ (A / dr x y ^ q) * M :=
        mul_le_mul (hK.size x hx y hy) hv (abs_nonneg _)
          (div_nonneg hK.A_nonneg (pow_nonneg (hS.dr_nonneg x hx y hy) _))
    _ = A * M / dr x y ^ q := by ring

/-- **Row integral** of the absolute value of the sliced kernel:
`∫_S |K x y| dy ≤ A Cv 2^(q+1) (2ρ)`. -/
theorem lintegral_enorm_row_le (hx : x ∈ S) :
    ∫⁻ y in S, ‖K x y‖ₑ ∂μ ≤ ENNReal.ofReal (A * (Cv * 2 ^ (q + 1)) * (2 * ρ)) := by
  refine le_trans (setLIntegral_mono' hS.measurableSet (g := fun y => ENNReal.ofReal (A / dr x y ^ q))
    fun y hy => ?_) (hS.lintegral_row_le hx hK.A_nonneg)
  have := hK.enorm_mul_le hS hx hy (v := 1) (M := 1) (by simp)
  simpa using this

/-- **Column integral** (by symmetry of `dr`):
`∫_S |K x y| dx ≤ A Cv 2^(q+1) (2ρ)`. -/
theorem lintegral_enorm_column_le {y : E} (hy : y ∈ S) :
    ∫⁻ x in S, ‖K x y‖ₑ ∂μ ≤ ENNReal.ofReal (A * (Cv * 2 ^ (q + 1)) * (2 * ρ)) := by
  refine le_trans (setLIntegral_mono' hS.measurableSet
    (g := fun x => ENNReal.ofReal (A / dr y x ^ q)) fun x hx => ?_) (hS.lintegral_row_le hy hK.A_nonneg)
  have := hK.enorm_mul_le hS hx hy (v := 1) (M := 1) (by simp)
  rw [hS.dr_symm x hx y hy] at this
  simpa using this

/-- A row against a bounded input is absolutely integrable
(`∫_S |K x y| |f y| dy ≤ A M Cv 2^(q+1) (2ρ)`). -/
theorem lintegral_enorm_mul_le {f : E → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y ∈ S, |f y| ≤ M)
    (hx : x ∈ S) :
    ∫⁻ y in S, ‖K x y * f y‖ₑ ∂μ ≤
      ENNReal.ofReal (A * M * (Cv * 2 ^ (q + 1)) * (2 * ρ)) :=
  (setLIntegral_mono' hS.measurableSet fun y hy => hK.enorm_mul_le hS hx hy (hM y hy)).trans
    (hS.lintegral_row_le hx (mul_nonneg hK.A_nonneg hM0))

/-- Rows against bounded measurable inputs are integrable on `S`. -/
theorem integrable_row {f : E → ℝ} (hf : AEStronglyMeasurable f (μ.restrict S)) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ S, |f y| ≤ M) (hx : x ∈ S) :
    Integrable (fun y => K x y * f y) (μ.restrict S) :=
  ⟨(hK.measurable.of_uncurry_left (x := x)).aestronglyMeasurable.mul hf,
    lt_of_le_of_lt (hK.lintegral_enorm_mul_le hS hM0 hM hx) ENNReal.ofReal_lt_top⟩

/-- **Sup bound** `‖𝓕_r f‖_∞ ≤ C ρ ‖f‖_∞` on `S`:
`|∫_S K x y f y dy| ≤ A M Cv 2^(q+1) (2ρ)` if `|f| ≤ M` on `S`. -/
theorem abs_integral_le {f : E → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y ∈ S, |f y| ≤ M)
    (hx : x ∈ S) :
    |∫ y in S, K x y * f y ∂μ| ≤ A * M * (Cv * 2 ^ (q + 1)) * (2 * ρ) := by
  have h1 := ofReal_abs_integral_le (fun y => K x y * f y) (μ.restrict S)
  have h2 := hK.lintegral_enorm_mul_le hS hM0 hM hx
  have hnn : 0 ≤ A * M * (Cv * 2 ^ (q + 1)) * (2 * ρ) := by
    have := hS.Cv_nonneg
    have := hS.ρ_pos
    have := hK.A_nonneg
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp (h1.trans h2)

/-- **The `L^p` bound for the restricted error**, `1 ≤ p < ∞`: by Schur's lemma
with row and column integrals `≤ Λ`, where `Λ ≥ A Cv 2^(q+1) (2ρ)`. The output is in
`L^p(S)` and `‖𝓕 f‖_p ≤ Λ ‖f‖_p`, with `Λ` independent of `p`. -/
theorem memLp_and_eLpNorm_le [SFinite μ] {Λ : ℝ} (hΛ : 0 < Λ)
    (hΛ' : A * (Cv * 2 ^ (q + 1)) * (2 * ρ) ≤ Λ) {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (μ.restrict S)) :
    MemLp (fun x => ∫ y, K x y * f y ∂(μ.restrict S)) (ENNReal.ofReal p) (μ.restrict S) ∧
      eLpNorm (fun x => ∫ y, K x y * f y ∂(μ.restrict S)) (ENNReal.ofReal p) (μ.restrict S) ≤
        ENNReal.ofReal Λ * eLpNorm f (ENNReal.ofReal p) (μ.restrict S) := by
  have hrow : ∀ x, ∫⁻ y, ‖K x y‖ₑ ∂(μ.restrict S) ≤ ENNReal.ofReal Λ := by
    intro x
    by_cases hx : x ∈ S
    · exact (hK.lintegral_enorm_row_le hS hx).trans (ENNReal.ofReal_le_ofReal hΛ')
    · simp [hK.zero_left x _ hx]
  have hcol : ∀ y, ∫⁻ x, ‖K x y‖ₑ ∂(μ.restrict S) ≤ ENNReal.ofReal Λ := by
    intro y
    by_cases hy : y ∈ S
    · exact (hK.lintegral_enorm_column_le hS hy).trans (ENNReal.ofReal_le_ofReal hΛ')
    · simp [hK.zero_right _ y hy]
  refine ⟨(integralOperator_memLp_and_integrable_ae (μ.restrict S) (μ.restrict S) K hK.measurable
    (ENNReal.ofReal Λ) (ENNReal.ofReal Λ) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hrow hcol f
    hp hf).1, ?_⟩
  have hb := integralOperator_schur_eLpNorm_bound (μ.restrict S) (μ.restrict S) K hK.measurable
    (ENNReal.ofReal Λ) (ENNReal.ofReal Λ) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hrow hcol f
    hp hf
  have hpos : ENNReal.ofReal Λ ≠ 0 := (ENNReal.ofReal_pos.mpr hΛ).ne'
  rwa [← ENNReal.rpow_add _ _ hpos ENNReal.ofReal_ne_top, sub_add_cancel, ENNReal.rpow_one] at hb

end SliceBounds

end RothschildStein.P1

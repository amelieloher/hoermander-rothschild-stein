-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitEstimatesHadamard
public import RothschildStein.P1.KernelEstimatesCutoff

/-!
# Estimates for the singular split `K = K₀ + K₁`

BB Prop 11.33 (pp. 572–576, (11.52)–(11.59)). For a degree-2 homogeneous
parameter family `D^{ξ,η}` (`SplitFamily`), a pole `Γ` smooth off `0` and homogeneous of degree
`2 - Q`, and a radial cutoff `χ = φ ∘ ν` of class `C¹`, on a compact `L ⊆ U`:

* `K₀(ξ, η) = k^{ξ,ξ}(Θ(η, ξ))/(1 + ω₋(ξ, Θ(η, ξ)))` has size `A d̃^{-Q}` and difference bound
  `S d̃(ξ, ξ')/d̃(ξ', η)^(Q+1)` (singular exponent 1, `HasKernelBounds L 0`): the kernel estimates with `ℓ = 0`
  for `k^{ξ,ξ}(Θ)`, times the smooth bounded density factor;
* the diagonal part `K₁ᵃ = k^{ξ,ξ}(Θ) ω₋/(1 + ω₋)` has `HasKernelBounds L 1` (size `A d̃^{1-Q}`,
  difference `S d̃(ξ, ξ')/d̃(ξ', η)^Q`; erratum: fractional exponents `(1, 1)`): the factor
  `ω₋/(1 + ω₋)` vanishes on the diagonal;
* the parameter part `E = [k^{ξ,η} - k^{ξ,ξ}](Θ)` has `HasKernelBounds L 1`: by the parameter
  mean value `E = ∑_l (η - ξ)_l V_l(ξ, η, Θ) χ(Θ)` with homogeneous `V_l` (the kernel estimates, `ℓ = 0`) and the
  vanishing factor `(η - ξ)_l`;
* hence `K₁ = K₁ᵃ + E` has `HasKernelBounds L 1`;
* the same for the transposed split `(K'₀, K'₁)` of the exchanged-and-reflected data
  `(transposeFamily D, Γ*)` (BB p. 576, Prop 11.33(d)), by instantiation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}
variable {L : Set (Fin (n + m) → ℝ)}
variable {ν : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
  {Γ : (Fin (n + m) → ℝ) → ℝ}

/-- The kernel `k^{ξ,ξ}(Θ(η, ξ))` of the singular split, with parameter evaluated on the diagonal, is the kernel
`χ(Θ(η, ξ)) W^{ξ,η}(Θ(η, ξ))` of the family `W^{ξ,η} = D^{ξ,ξ} Γ` with the cutoff `χ = φ ∘ ν`. -/
theorem kernelValue_diag_eq (ξ η : Fin (n + m) → ℝ) :
    C.kernelValue (fun u => φ (ν u)) (fun ξ _ u => (D ξ ξ).apply Γ u) ξ η =
      cutoffKernel ν D Γ φ ξ ξ (C.Θ η ξ) := by
  unfold kernelValue cutoffKernel
  ring

/-- The kernel estimates for the diagonal kernel `k^{ξ,ξ}(Θ(η, ξ))`: singular exponent 1. -/
theorem hasKernelBounds_cutoffDiag (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hΓh : ∀ t : ℝ, 0 < t → ∀ x : Fin (n + m) → ℝ, x ≠ 0 →
      Γ (C.G.dilate t x) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ x)
    (hχ : ContDiff ℝ 1 (fun u => φ (ν u)))
    (hL : IsCompact L) (hLU : L ⊆ C.U) :
    C.HasKernelBounds L 0 (fun ξ η => cutoffKernel ν D Γ φ ξ ξ (C.Θ η ξ)) := by
  have h := hasKernelBounds_kernelValue_zero (C := C) (L := L) hχ
    ((F.contDiffOn_kernelUncurry_diag hΓ).of_le (by simp))
    (fun ξ η t ht u hu => F.apply_dilate hΓ hΓh ξ ξ ht hu) hL hLU
  exact h.congr (fun ξ _ η _ => kernelValue_diag_eq ξ η)

/-- **`K₀` is a singular kernel of exponent 1** (BB pp. 573–574,
Prop 11.33(b)): `|K₀(ξ, η)| ≤ A₀ d̃(ξ, η)^(-Q)` and
`|K₀(ξ', η) - K₀(ξ, η)| + |K₀(η, ξ') - K₀(η, ξ)| ≤ S₀ d̃(ξ, ξ')/d̃(ξ', η)^(Q+1)` when
`d̃(ξ', η) > 2 d̃(ξ, ξ')`, uniformly on a compact `L ⊆ U`. The kernel estimates with `ℓ = 0` for `k^{ξ,ξ}(Θ)`,
multiplied by the smooth positive density factor `1/(1 + ω₋)` (bounded with `d̃`-Lipschitz
differences; "absorbed on the fixed patch"). -/
theorem hasKernelBounds_splitK0 (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hΓh : ∀ t : ℝ, 0 < t → ∀ x : Fin (n + m) → ℝ, x ≠ 0 →
      Γ (C.G.dilate t x) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ x)
    (hχ : ContDiff ℝ 1 (fun u => φ (ν u)))
    (hL : IsCompact L) (hLU : L ⊆ C.U) :
    C.HasKernelBounds L 0 (C.splitK0 ν D Γ φ) := by
  have h := HasKernelBounds.mul_of_contDiffOn hL hLU (g := C.densityFactor)
    C.contDiffOn_densityFactor (hasKernelBounds_cutoffDiag F hΓ hΓh hχ hL hLU)
  exact h.congr (fun ξ _ η _ => by
    simp only [splitK0, densityFactor, div_eq_inv_mul])

/-- **The diagonal part of `K₁` has fractional exponents `(1, 1)`**
(BB pp. 574–575): `K₁ᵃ(ξ, η) = k^{ξ,ξ}(Θ(η, ξ)) f(ξ, Θ(η, ξ))`, `f = ω₋/(1 + ω₋)`, has
`|K₁ᵃ| ≤ A d̃^(1-Q)` and `|K₁ᵃ(ξ', η) - K₁ᵃ(ξ, η)| + |K₁ᵃ(η, ξ') - K₁ᵃ(η, ξ)| ≤
S d̃(ξ, ξ')/d̃(ξ', η)^Q` for `d̃(ξ', η) > 2 d̃(ξ, ξ')`. The factor `f` vanishes on the diagonal
(`ω₋(ξ, 0) = 0`), so `|f| = O(d̃)` and its differences are `O(d̃(ξ, ξ'))`: singular difference
`O(h r^(-Q-1))` times `O(r)`, plus size `O(r^(-Q))` times `O(h)`. -/
theorem hasKernelBounds_splitK1Diag (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hΓh : ∀ t : ℝ, 0 < t → ∀ x : Fin (n + m) → ℝ, x ≠ 0 →
      Γ (C.G.dilate t x) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ x)
    (hχ : ContDiff ℝ 1 (fun u => φ (ν u)))
    (hL : IsCompact L) (hLU : L ⊆ C.U) :
    C.HasKernelBounds L 1 (C.splitK1Diag ν D Γ φ) := by
  have h := HasKernelBounds.mul_of_contDiffOn_diag hL hLU
    (g := fun ξ η => C.diagFactor ξ (C.Θ η ξ)) C.contDiffOn_diagFactor_theta
    (fun ξ hξ => C.diagFactor_theta_self (hLU hξ)) (hasKernelBounds_cutoffDiag F hΓ hΓh hχ hL hLU)
  exact h.congr (fun ξ _ η _ => by
    rw [splitK1Diag_eq, mul_comm])

/-- The parameter part of `K₁` through the parameter mean value:
`E(ξ, η) = ∑_l (η_l - ξ_l) · χ(Θ(η, ξ)) V_l(ξ, η, Θ(η, ξ))` (BB pp. 575–576). -/
theorem splitK1Param_eq_sum (F : SplitFamily C.G D) (ξ η : Fin (n + m) → ℝ) :
    C.splitK1Param ν D Γ φ ξ η =
      ∑ l, (η l - ξ l) * C.kernelValue (fun u => φ (ν u))
        (fun ξ η u => F.hadamardKernel Γ l ξ η u) ξ η := by
  unfold splitK1Param cutoffKernel kernelValue
  rw [← sub_mul, F.apply_sub_eq_sum Γ ξ η (C.Θ η ξ), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

/-- **The parameter part of `K₁` has fractional exponents `(1, 1)`**
(BB pp. 575–576, (11.59); erratum: denominator `d̃^Q`): `E = [k^{ξ,η} - k^{ξ,ξ}](Θ(η, ξ))` has
`|E| ≤ A d̃^(1-Q)` and `|E(ξ', η) - E(ξ, η)| + |E(η, ξ') - E(η, ξ)| ≤
S d̃(ξ, ξ')/d̃(ξ', η)^Q` for `d̃(ξ', η) > 2 d̃(ξ, ξ')`. The parameter mean value writes
`E = ∑_l (η - ξ)_l χ(Θ) V_l(ξ, η, Θ)` with jointly smooth, degree `-Q` homogeneous `V_l`
(`SplitFamily.hadamardKernel`), so that the kernel estimates (`ℓ = 0`; horizontal and drift derivative bounds,
path argument) applies to `V_l`, and the factor `(η - ξ)_l`, vanishing on the diagonal, gains one
power of `d̃` (`|ξ - η| ≤ C ρ`). -/
theorem hasKernelBounds_splitK1Param (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hΓh : ∀ t : ℝ, 0 < t → ∀ x : Fin (n + m) → ℝ, x ≠ 0 →
      Γ (C.G.dilate t x) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ x)
    (hχ : ContDiff ℝ 1 (fun u => φ (ν u)))
    (hL : IsCompact L) (hLU : L ⊆ C.U) :
    C.HasKernelBounds L 1 (C.splitK1Param ν D Γ φ) := by
  have hl : ∀ l : Fin (n + m), C.HasKernelBounds L (0 + 1) (fun ξ η => (η l - ξ l) *
      C.kernelValue (fun u => φ (ν u)) (fun ξ η u => F.hadamardKernel Γ l ξ η u) ξ η) := by
    intro l
    have hκ := hasKernelBounds_kernelValue_zero (C := C) (L := L) hχ
      ((F.contDiffOn_kernelUncurry_hadamard hΓ l).of_le (by simp))
      (fun ξ η t ht u hu => F.hadamardKernel_dilate Γ hΓ hΓh l ξ η ht hu) hL hLU
    have hg : ContDiffOn ℝ 1 (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => p.2 l - p.1 l)
        (C.U ×ˢ C.U) :=
      (((contDiff_apply ℝ ℝ l).comp contDiff_snd).sub
        ((contDiff_apply ℝ ℝ l).comp contDiff_fst)).contDiffOn
    exact HasKernelBounds.mul_of_contDiffOn_diag hL hLU (g := fun ξ η => η l - ξ l) hg
      (fun ξ _ => sub_self _) hκ
  have hsum := HasKernelBounds.finset_sum (C := C) (L := L) Finset.univ (fun l _ => hl l)
  exact hsum.congr (fun ξ _ η _ => (splitK1Param_eq_sum F ξ η).symm)

/-- **`K₁` has fractional exponents `(1, 1)`** (BB Prop 11.33(c), pp. 574–576; erratum:
size `d̃^(1-Q)`, difference denominator `d̃^Q`): the sum of the diagonal and parameter parts
(`splitK1_eq_diag_add_param`). -/
theorem hasKernelBounds_splitK1 (F : SplitFamily C.G D)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hΓh : ∀ t : ℝ, 0 < t → ∀ x : Fin (n + m) → ℝ, x ≠ 0 →
      Γ (C.G.dilate t x) = t ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ x)
    (hχ : ContDiff ℝ 1 (fun u => φ (ν u)))
    (hL : IsCompact L) (hLU : L ⊆ C.U) :
    C.HasKernelBounds L 1 (C.splitK1 ν D Γ φ) := by
  have h := (hasKernelBounds_splitK1Diag F hΓ hΓh hχ hL hLU).add
    (hasKernelBounds_splitK1Param F hΓ hΓh hχ hL hLU)
  exact h.congr (fun ξ _ η _ => (splitK1_eq_diag_add_param ξ η).symm)

end LiftedChart
end RothschildStein.P1

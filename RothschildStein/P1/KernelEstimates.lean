-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesDifference
public import RothschildStein.P1.KernelEstimatesCutoff

/-!
# Lifted homogeneous kernel estimates

Let `W ξ η u` be jointly `C¹` on `{u ≠ 0}` and homogeneous of degree `ℓ - Q` in `u` for the model
dilations, `Q` the homogeneous dimension of the model group, and `K(ξ, η) = W^{ξ,η}(Θ(η, ξ))`,
optionally multiplied by a `C¹` cutoff `χ(Θ(η, ξ))` of the group variable (a smooth radial
cutoff). Uniformly for `ξ, ξ', η` in a compact subset of the lifted coordinate neighborhood:

* size `|K(ξ, η)| ≤ A d̃(ξ, η)^(ℓ - Q)`;
* difference `|K(ξ', η) - K(ξ, η)| + |K(η, ξ') - K(η, ξ)| ≤ B d̃(ξ, ξ') / d̃(ξ', η)^(Q + 1 - ℓ)`
  whenever `d̃(ξ', η) > 2 d̃(ξ, ξ')`;
* derivative bounds `|X̃_{i,ξ} K(ξ, η)| ≤ M d̃(ξ, η)^(ℓ - Q - w_i)`.

The chart is any `LiftedChart` (drift or no drift: the fields are `Fin k` with weights `w`).
The second variable is the first applied to `Ŵ^{ξ,η}(u) = W^{η,ξ}(-u)`, using `Θ(ξ, η) = -Θ(η, ξ)`
(BB pp. 569–571, Prop 11.32, (11.49)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The lifted kernel `K(ξ, η) = χ(Θ(η, ξ)) W^{ξ,η}(Θ(η, ξ))` of a homogeneous family
`W` with a cutoff `χ` of the group variable (BB p. 569, Prop 11.32). -/
def kernelValue (χ : (Fin (n + m) → ℝ) → ℝ)
    (W : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (ξ η : Fin (n + m) → ℝ) : ℝ :=
  χ (C.Θ η ξ) * W ξ η (C.Θ η ξ)

/-- The size and difference estimates for two families related by the reflection
`Ψ̂^{ξ,η}(u) = Ψ^{η,ξ}(-u)`, from their weighted bounds. -/
theorem exists_kernel_estimates_of_weighted
    {Ψ Ψ' : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {d : ℤ}
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0}) (hWB : HasWeightedBounds C.G d Ψ)
    (hΨ' : ContDiffOn ℝ 1 (kernelUncurry Ψ') {z | z.2.2 ≠ 0})
    (hWB' : HasWeightedBounds C.G d Ψ')
    (hswap : ∀ ξ ∈ C.U, ∀ η ∈ C.U, Ψ' ξ η (C.Θ η ξ) = Ψ η ξ (C.Θ ξ η))
    {K₀ : Set (Fin (n + m) → ℝ)} (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ ξ ∈ K₀, ∀ η ∈ K₀, ξ ≠ η → |Ψ ξ η (C.Θ η ξ)| ≤ A * (C.dl ξ η).toReal ^ d) ∧
      (∀ ξ ∈ K₀, ∀ ξ' ∈ K₀, ∀ η ∈ K₀, 2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
        |Ψ ξ' η (C.Θ η ξ') - Ψ ξ η (C.Θ η ξ)| + |Ψ η ξ' (C.Θ ξ' η) - Ψ η ξ (C.Θ ξ η)| ≤
          B * ((C.dl ξ ξ').toReal * (C.dl ξ' η).toReal ^ (d - 1))) := by
  obtain ⟨A, hA0, hA⟩ := C.exists_size_bound hWB hK₀ hK₀U
  obtain ⟨B₁, hB₁0, hB₁⟩ := C.exists_difference_bound_first hΨ hWB hK₀ hK₀U
  obtain ⟨B₂, hB₂0, hB₂⟩ := C.exists_difference_bound_first hΨ' hWB' hK₀ hK₀U
  refine ⟨A, B₁ + B₂, hA0, add_nonneg hB₁0 hB₂0, hA, ?_⟩
  intro ξ hξ ξ' hξ' η hη hsep
  have h1 := hB₁ ξ hξ ξ' hξ' η hη hsep
  have h2 := hB₂ ξ hξ ξ' hξ' η hη hsep
  rw [hswap ξ' (hK₀U hξ') η (hK₀U hη), hswap ξ (hK₀U hξ) η (hK₀U hη)] at h2
  calc _ ≤ B₁ * ((C.dl ξ ξ').toReal * (C.dl ξ' η).toReal ^ (d - 1)) +
        B₂ * ((C.dl ξ ξ').toReal * (C.dl ξ' η).toReal ^ (d - 1)) := add_le_add h1 h2
    _ = _ := by ring

section Homogeneous

variable {W : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {ℓ : ℕ}
  {χ : (Fin (n + m) → ℝ) → ℝ}

/-- The kernel `Ψ = χ(u) W` of a cutoff times a `C¹` family is `C¹` off `u = 0`. -/
theorem cutoff_mul_contDiffOn (hχ : ContDiff ℝ 1 χ)
    (hW : ContDiffOn ℝ 1 (kernelUncurry W) {z | z.2.2 ≠ 0}) :
    ContDiffOn ℝ 1 (kernelUncurry (fun ξ η u => χ u * W ξ η u)) {z | z.2.2 ≠ 0} :=
  (hχ.comp contDiff_snd.snd).contDiffOn.mul hW

/-- The reflected family `Ŵ^{ξ,η}(u) = W^{η,ξ}(-u)` is `C¹` off `u = 0`. -/
theorem reflect_contDiffOn (hW : ContDiffOn ℝ 1 (kernelUncurry W) {z | z.2.2 ≠ 0}) :
    ContDiffOn ℝ 1 (kernelUncurry (fun ξ η u => W η ξ (-u))) {z | z.2.2 ≠ 0} := by
  have hA : ContDiff ℝ 1 (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      (z.2.1, z.1, -z.2.2)) :=
    contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd.neg)
  exact hW.comp hA.contDiffOn (fun z hz => by simpa using hz)

/-- The reflected family keeps the homogeneity degree (`D_λ(-u) = -D_λ(u)`). -/
theorem reflect_homogeneous {d : ℤ}
    (hhom : ∀ ξ η : Fin (n + m) → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      W ξ η (C.G.dilate t u) = t ^ d * W ξ η u) :
    ∀ ξ η : Fin (n + m) → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      (fun ξ η u => W η ξ (-u)) ξ η (C.G.dilate t u) = t ^ d * (fun ξ η u => W η ξ (-u)) ξ η u := by
  intro ξ η t ht u hu
  have hu' : -u ≠ 0 := neg_ne_zero.mpr hu
  show W η ξ (-C.G.dilate t u) = t ^ d * W η ξ (-u)
  rw [← kdilate_neg]
  exact hhom η ξ t ht (-u) hu'

/-- **Lifted homogeneous kernel estimates** (BB pp. 569–571, Prop 11.32, (11.49): size and
difference bounds, the latter in both variables). Let `W^{ξ,η}(u)` be jointly `C¹` off `u = 0` and homogeneous of degree
`ℓ - Q`, `K(ξ, η) = χ(Θ(η, ξ)) W^{ξ,η}(Θ(η, ξ))` with a `C¹` cutoff `χ` of the group variable
(`χ ≡ 1` is the uncut kernel). Uniformly for `ξ, ξ', η` in a compact `K₀ ⊆ U`:
`|K(ξ, η)| ≤ A d̃(ξ, η)^(ℓ - Q)` and, if `d̃(ξ', η) > 2 d̃(ξ, ξ')`,
`|K(ξ', η) - K(ξ, η)| + |K(η, ξ') - K(η, ξ)| ≤ B d̃(ξ, ξ') / d̃(ξ', η)^(Q + 1 - ℓ)`. -/
theorem exists_kernel_estimates_cutoff (hχ : ContDiff ℝ 1 χ)
    (hW : ContDiffOn ℝ 1 (kernelUncurry W) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin (n + m) → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      W ξ η (C.G.dilate t u) = t ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ)) * W ξ η u)
    {K₀ : Set (Fin (n + m) → ℝ)} (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ ξ ∈ K₀, ∀ η ∈ K₀, ξ ≠ η → |C.kernelValue χ W ξ η| ≤
        A * (C.dl ξ η).toReal ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ))) ∧
      (∀ ξ ∈ K₀, ∀ ξ' ∈ K₀, ∀ η ∈ K₀, 2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
        |C.kernelValue χ W ξ' η - C.kernelValue χ W ξ η| +
          |C.kernelValue χ W η ξ' - C.kernelValue χ W η ξ| ≤
          B * (C.dl ξ ξ').toReal /
            (C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ))) := by
  set d : ℤ := (ℓ : ℤ) - (C.G.homogeneousDimension : ℤ) with hd
  have hWB : HasWeightedBounds C.G d W := hasWeightedBounds_of_homogeneous hW hhom
  have hΨ := cutoff_mul_contDiffOn hχ hW
  have hWB1 : HasWeightedBounds C.G d (fun ξ η u => χ u * W ξ η u) := hWB.cutoff_mul hχ hW
  have hŴ := reflect_contDiffOn hW
  have hWB' : HasWeightedBounds C.G d (fun ξ η u => W η ξ (-u)) :=
    hasWeightedBounds_of_homogeneous hŴ (reflect_homogeneous C hhom)
  have hχ' : ContDiff ℝ 1 (fun u : Fin (n + m) → ℝ => χ (-u)) := hχ.comp contDiff_neg
  have hΨ' := cutoff_mul_contDiffOn hχ' hŴ
  have hWB2 : HasWeightedBounds C.G d (fun ξ η u => χ (-u) * W η ξ (-u)) :=
    hWB'.cutoff_mul hχ' hŴ
  have hswap : ∀ ξ ∈ C.U, ∀ η ∈ C.U,
      (fun ξ η u => χ (-u) * W η ξ (-u)) ξ η (C.Θ η ξ) =
        (fun ξ η u => χ u * W ξ η u) η ξ (C.Θ ξ η) := by
    intro ξ hξ η hη
    simp only [C.theta_antisymm η hη ξ hξ]
  obtain ⟨A, B, hA0, hB0, hA, hB⟩ := C.exists_kernel_estimates_of_weighted hΨ hWB1 hΨ' hWB2
    hswap hK₀ hK₀U
  refine ⟨A, B, hA0, hB0, hA, ?_⟩
  intro ξ hξ ξ' hξ' η hη hsep
  have h := hB ξ hξ ξ' hξ' η hη hsep
  have hr : 0 < (C.dl ξ' η).toReal := by linarith [ENNReal.toReal_nonneg (a := C.dl ξ ξ')]
  have hpow : (C.dl ξ' η).toReal ^ (d - 1) =
      ((C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)))⁻¹ := by
    rw [← zpow_neg]
    congr 1
    rw [hd]
    ring
  rw [hpow, ← div_eq_mul_inv] at h
  have hrw : B * ((C.dl ξ ξ').toReal / (C.dl ξ' η).toReal ^
      ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ))) = B * (C.dl ξ ξ').toReal /
      (C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ)) := by ring
  rw [hrw] at h
  exact h

/-- The uncut case of `exists_kernel_estimates_cutoff`: `K(ξ, η) = W^{ξ,η}(Θ(η, ξ))`. -/
theorem exists_kernel_estimates
    (hW : ContDiffOn ℝ 1 (kernelUncurry W) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η : Fin (n + m) → ℝ, ∀ t : ℝ, 0 < t → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      W ξ η (C.G.dilate t u) = t ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ)) * W ξ η u)
    {K₀ : Set (Fin (n + m) → ℝ)} (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ ξ ∈ K₀, ∀ η ∈ K₀, ξ ≠ η → |W ξ η (C.Θ η ξ)| ≤
        A * (C.dl ξ η).toReal ^ ((ℓ : ℤ) - (C.G.homogeneousDimension : ℤ))) ∧
      (∀ ξ ∈ K₀, ∀ ξ' ∈ K₀, ∀ η ∈ K₀, 2 * (C.dl ξ ξ').toReal < (C.dl ξ' η).toReal →
        |W ξ' η (C.Θ η ξ') - W ξ η (C.Θ η ξ)| +
          |W η ξ' (C.Θ ξ' η) - W η ξ (C.Θ ξ η)| ≤
          B * (C.dl ξ ξ').toReal /
            (C.dl ξ' η).toReal ^ ((C.G.homogeneousDimension : ℤ) + 1 - (ℓ : ℤ))) := by
  obtain ⟨A, B, hA0, hB0, hA, hB⟩ := C.exists_kernel_estimates_cutoff (χ := fun _ => (1 : ℝ))
    contDiff_const hW hhom hK₀ hK₀U
  refine ⟨A, B, hA0, hB0, ?_, ?_⟩
  · intro ξ hξ η hη hne
    simpa only [kernelValue, one_mul] using hA ξ hξ η hη hne
  · intro ξ hξ ξ' hξ' η hη hsep
    simpa only [kernelValue, one_mul] using hB ξ hξ ξ' hξ' η hη hsep

end Homogeneous

end LiftedChart
end RothschildStein.P1

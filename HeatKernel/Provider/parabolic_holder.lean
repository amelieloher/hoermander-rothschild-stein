-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderParabolicComparison

/-! # Parabolic Hölder continuity on horizontal coordinate balls -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter RothschildStein
open scoped BigOperators Topology ENNReal NNReal
namespace HeatKernel.Provider

/-- Local weak solutions of measurable uniformly elliptic symmetric matrix
equations have a continuous representative and a uniform parabolic Hölder modulus. -/
theorem parabolic_holder
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    let d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ :=
      fun x y => (horizontalL2Distance X x y).toReal
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
        (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)) →
        (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
          (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧
          ∀ ξ : Fin q → ℝ,
            lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
            ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2) →
      ∀ (x₀ : Fin N → ℝ) (r t₀ : ℝ), 0 < r →
      ∀ u : ℝ → (Fin N → ℝ) → ℝ,
        IsLocalWeakSolution G hq hqpos hw hspan a ⟨Ioo (t₀ - 4 * r ^ 2) t₀, isOpen_Ioo⟩
          ⟨interior (B x₀ (2 * r)), isOpen_interior⟩ u →
        ∃ v : ℝ → (Fin N → ℝ) → ℝ,
          (∀ᵐ z ∂(volume.restrict (Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r)), v z.1 z.2 = u z.1 z.2) ∧
          ContinuousOn (fun z : ℝ × (Fin N → ℝ) => v z.1 z.2) (Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r) ∧
          ∀ m M : ℝ,
            (∀ᵐ z ∂(volume.restrict (Ioo (t₀ - 4 * r ^ 2) t₀ ×ˢ B x₀ (2 * r))),
              m ≤ u z.1 z.2 ∧ u z.1 z.2 ≤ M) →
            ∀ z ∈ Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r, ∀ w ∈ Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r,
              |v z.1 z.2 - v w.1 w.2| ≤
                C * ((d z.2 w.2 + Real.sqrt |z.1 - w.1|) / r) ^ α * (M - m) :=
  HeatKernel.exists_uniform_matrix_parabolic_holder G hq hqpos hw hspan lam Λ hlam hlamΛ

end HeatKernel.Provider

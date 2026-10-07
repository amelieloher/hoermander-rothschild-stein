-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.S
variable {n : ℕ}

/-- The support of a flow pullback lies in the reverse-time image of the test support (BB Proposition 2.22, pp. 89–90). -/
theorem flow_pullback_support_subset
    {Ω U K C : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    (hKU : K ⊆ U) (φ : (Fin n → ℝ) → ℝ) (hφ : Function.support φ ⊆ K)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hC : ∀ y ∈ K,Φ (y,-t) ∈ C) :
    U ∩ Function.support (fun x => φ (Φ (x,t))) ⊆ C := by
  intro x hx
  have hy : Φ (x,t) ∈ K := hφ hx.2
  have he := G1.localFlow_inverse hΩ hX hτ Φ hΦ hx.1 ht (hKU hy)
  exact he ▸ hC (Φ (x,t)) hy

/-- The difference of a pulled-back test and the original
has support in one common compact buffer, provided that buffer contains
K and its reverse-time flow image (BB pp. 89–90). -/
theorem flow_test_difference_support_subset
    {Ω U K C : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    (hKU : K ⊆ U) (hKC : K ⊆ C)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Function.support φ ⊆ K)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hC : ∀ y ∈ K,Φ (y,-t) ∈ C) :
    U ∩ Function.support (fun x => φ (Φ (x,t))-φ x) ⊆ C := by
  intro x hx
  by_cases hp : φ (Φ (x,t)) = 0
  · apply hKC
    apply hφ
    intro hz
    exact hx.2 (by simp only [hp,hz,sub_self])
  · exact flow_pullback_support_subset hΩ hX hτ Φ hΦ hKU φ hφ ht hC ⟨hx.1,hp⟩

end RothschildStein.S

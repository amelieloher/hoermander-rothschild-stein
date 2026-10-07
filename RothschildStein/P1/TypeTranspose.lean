-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalTranspose
public import RothschildStein.P1.RegularTranspose

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1

/-- The principal transpose identity extends to every pair of
endpoints: outside either cutoff both sides vanish. Only the actual local
chart identities and the punctured H1 pole relation are used. -/
theorem PrincipalTerm.transpose_kernel_global {N : ℕ} {F : KernelFrame N}
    (t : PrincipalTerm F)
    (hpole : ∀ b : Bool, ∀ u : Fin N → ℝ, u ≠ 0 → F.pole (!b) u = F.pole b (-u))
    (hsmooth : ∀ b : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole b) {(0 : Fin N → ℝ)}ᶜ)
    (hanti : ∀ ξ ∈ F.V, ∀ η ∈ F.V, F.Θ η ξ = -F.Θ ξ η)
    (hne : ∀ ξ ∈ F.V, ∀ η ∈ F.V, ξ ≠ η → F.Θ ξ η ≠ 0)
    (ξ η : Fin N → ℝ) (hξη : ξ ≠ η) :
    t.transpose.kernel ξ η = t.kernel η ξ := by
  by_cases ha : t.a η = 0
  · simp only [PrincipalTerm.kernel, PrincipalTerm.transpose, ha, mul_zero, zero_mul]
  by_cases hb : t.b ξ = 0
  · simp only [PrincipalTerm.kernel, PrincipalTerm.transpose, hb, mul_zero, zero_mul]
  have hη : η ∈ F.V := t.a.tsupport_subset (subset_tsupport t.a ha)
  have hξ : ξ ∈ F.V := t.b.tsupport_subset (subset_tsupport t.b hb)
  exact t.transpose_kernel hpole hsmooth ξ η (hne ξ hξ η hη hξη) (hanti ξ hξ η hη)

/-- Transposing an actual finite type decomposition preserves its
exact type and every requested regularity budget (BB pp. 545–546). -/
def TypeDecomposition.transpose {N lam m : ℕ} {F : KernelFrame N}
    {κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (D : TypeDecomposition F lam m κ)
    (hpole : ∀ b : Bool, ∀ u : Fin N → ℝ, u ≠ 0 → F.pole (!b) u = F.pole b (-u))
    (hsmooth : ∀ b : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole b) {(0 : Fin N → ℝ)}ᶜ)
    (hanti : ∀ ξ ∈ F.V, ∀ η ∈ F.V, F.Θ η ξ = -F.Θ ξ η)
    (hne : ∀ ξ ∈ F.V, ∀ η ∈ F.V, ξ ≠ η → F.Θ ξ η ≠ 0) :
    TypeDecomposition F lam m (fun ξ η => κ η ξ) where
  principal := D.principal.map PrincipalTerm.transpose
  principal_degree := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact D.principal_degree q hq
  regular ξ η := D.regular η ξ
  regular_isRegular := D.regular_isRegular.transpose
  eq_off_diagonal := by
    intro ξ η hξη
    rw [D.eq_off_diagonal η ξ (Ne.symm hξη)]
    congr 1
    simp only [List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    exact (t.transpose_kernel_global hpole hsmooth hanti hne ξ η hξη).symm

/-- Every type-λ kernel has a transposed kernel of the same type;
the construction works separately at every finite regularity budget. -/
theorem IsTypeKernel.transpose {N lam : ℕ} {F : KernelFrame N}
    {κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hκ : IsTypeKernel F lam κ)
    (hpole : ∀ b : Bool, ∀ u : Fin N → ℝ, u ≠ 0 → F.pole (!b) u = F.pole b (-u))
    (hsmooth : ∀ b : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole b) {(0 : Fin N → ℝ)}ᶜ)
    (hanti : ∀ ξ ∈ F.V, ∀ η ∈ F.V, F.Θ η ξ = -F.Θ ξ η)
    (hne : ∀ ξ ∈ F.V, ∀ η ∈ F.V, ξ ≠ η → F.Θ ξ η ≠ 0) :
    IsTypeKernel F lam (fun ξ η => κ η ξ) := by
  intro m
  obtain ⟨D⟩ := hκ m
  exact ⟨D.transpose hpole hsmooth hanti hne⟩

end RothschildStein.P1

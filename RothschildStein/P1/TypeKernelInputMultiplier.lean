-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeClosure
public import RothschildStein.S.Locality
public import RothschildStein.Definitions.testMultiplierOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1
variable {N budget lam : ℕ} {F : KernelFrame N}

/-- Locally smooth input multipliers preserve a regular kernel's
global regularity and compact interior support. -/
theorem IsRegularKernel.inputMultiplier
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsRegularKernel F budget r)
    (g : (Fin N → ℝ) → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (F.V : Set (Fin N → ℝ))) :
    IsRegularKernel F budget (fun ξ η => r ξ η * g η) := by
  let f := fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2
  let K : Compacts (Fin N → ℝ) := ⟨Prod.snd '' tsupport f,
    hr.2.1.isCompact.image continuous_snd⟩
  have hKV : (K : Set (Fin N → ℝ)) ⊆ F.V := by
    rintro η ⟨z, hz, rfl⟩
    exact (hr.2.2 hz).2
  obtain ⟨χ, U, _, hKU, _, hone⟩ := S.exists_test_plateau F.V K hKV
  let G := testMultiplierOn F.V g hg χ
  have hG (η : Fin N → ℝ) (hη : η ∈ (K : Set (Fin N → ℝ))) : G η = g η := by
    change χ η * g η = g η
    rw [hone (hKU hη)]
    exact one_mul _
  have he : (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2 * g z.2) =
      fun z => f z * G z.2 := by
    funext z
    by_cases hz : z ∈ tsupport f
    · rw [hG z.2 ⟨z, hz, rfl⟩]
    · have hz0 : r z.1 z.2 = 0 := image_eq_zero_of_notMem_tsupport (f := f) (x := z) hz
      simp only [f, hz0, zero_mul]
  have hs : tsupport (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2 * g z.2) ⊆
      tsupport f := tsupport_mul_subset_left
  refine ⟨?_, hr.2.1.mul_right, hs.trans hr.2.2⟩
  rw [he]
  exact hr.1.mul ((G.contDiff.of_le (by simp)).comp contDiff_snd)

/-- Absorb the input multiplier into the existing cutoff. -/
def PrincipalTerm.inputMultiplier (t : PrincipalTerm F) (g : (Fin N → ℝ) → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (F.V : Set (Fin N → ℝ))) : PrincipalTerm F :=
  {t with b := testMultiplierOn F.V g hg t.b}

/-- The absorbed principal cutoff gives exactly the multiplied kernel. -/
theorem PrincipalTerm.inputMultiplier_kernel (t : PrincipalTerm F) (g : (Fin N → ℝ) → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (F.V : Set (Fin N → ℝ))) (ξ η : Fin N → ℝ) :
    (t.inputMultiplier g hg).kernel ξ η = t.kernel ξ η * g η := by
  dsimp only [inputMultiplier, PrincipalTerm.kernel]
  change t.a ξ * (t.b η * g η) * (t.D ξ η).apply (F.pole t.star) (F.Θ η ξ) =
    (t.a ξ * t.b η * (t.D ξ η).apply (F.pole t.star) (F.Θ η ξ)) * g η
  ring

/-- Input multiplication by a coefficient smooth on V preserves
the full type at every regularity budget. -/
theorem IsTypeKernel.inputMultiplier
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsTypeKernel F lam r)
    (g : (Fin N → ℝ) → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (F.V : Set (Fin N → ℝ))) :
    IsTypeKernel F lam (fun ξ η => r ξ η * g η) := by
  intro budget
  obtain ⟨d⟩ := hr budget
  refine ⟨{
    principal := d.principal.map (fun t => t.inputMultiplier g hg)
    principal_degree := ?_
    regular := fun ξ η => d.regular ξ η * g η
    regular_isRegular := d.regular_isRegular.inputMultiplier g hg
    eq_off_diagonal := ?_ }⟩
  · intro t ht
    obtain ⟨u, hu, he⟩ := List.mem_map.mp ht
    rw [← he]
    exact d.principal_degree u hu
  · intro ξ η hne
    rw [d.eq_off_diagonal ξ η hne, add_mul]
    simp only [List.map_map, Function.comp_def, PrincipalTerm.inputMultiplier_kernel,
      List.sum_map_mul_right]

end RothschildStein.P1

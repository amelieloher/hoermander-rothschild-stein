-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
variable {N lam : ℕ} {F : KernelFrame N}

/-- Off the diagonal a type kernel vanishes when either endpoint
lies outside its cutoff region. No condition on diagonal values is used. -/
theorem IsTypeKernel.eq_zero_of_outside
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsTypeKernel F lam r)
    {ξ η : Fin N → ℝ} (hne : ξ ≠ η)
    (hout : ξ ∉ (F.V : Set (Fin N → ℝ)) ∨ η ∉ (F.V : Set (Fin N → ℝ))) :
    r ξ η = 0 := by
  obtain ⟨d⟩ := hr 0
  rw [d.eq_off_diagonal ξ η hne]
  have hp (t : PrincipalTerm F) : t.kernel ξ η = 0 := by
    rcases hout with hξ | hη
    · have ha : t.a ξ = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hξ (t.a.tsupport_subset h))
      simp only [PrincipalTerm.kernel, ha, zero_mul]
    · have hb : t.b η = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hη (t.b.tsupport_subset h))
      simp only [PrincipalTerm.kernel, hb, mul_zero, zero_mul]
  have hreg : d.regular ξ η = 0 := image_eq_zero_of_notMem_tsupport
    (f := fun z : (Fin N → ℝ) × (Fin N → ℝ) => d.regular z.1 z.2) (x := (ξ, η)) (fun h => by
    have hs := d.regular_isRegular.2.2 h
    rcases hout with hξ | hη
    · exact hξ hs.1
    · exact hη hs.2)
  simp only [hp, List.map_const', List.sum_replicate, nsmul_zero, hreg, add_zero]

end RothschildStein.P1

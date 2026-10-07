-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalHomogeneousMultiplier
public import RothschildStein.P1.RegularKernelModelMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Multiplication by a smooth homogeneous model coefficient of
nonnegative degree d raises the full kernel type from λ to λ+d, at every
regularity budget (BB Lemma 11.23 and Theorem 11.24, pp. 554–558). -/
theorem LiftedChart.isTypeKernel_homogeneousModelMultiplier
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U)
    {lam : ℕ} {κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) (g : (Fin (n+m) → ℝ) → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (d : ℕ)
    (hd : ∀ r : ℝ, 0 < r → ∀ u, g (F.G.dilate r u) = r ^ (d : ℝ) * g u) :
    IsTypeKernel F (lam+d) (fun ξ η => g (F.Θ η ξ) * κ ξ η) := by
  intro budget
  obtain ⟨D⟩ := hκ budget
  let terms := D.principal.map (fun t => t.multiplyHomogeneousModel g hg (d : ℤ)
    (by simpa only [Int.cast_natCast] using hd))
  refine ⟨{
    principal := terms
    principal_degree := ?_
    regular := fun ξ η => g (F.Θ η ξ) * D.regular ξ η
    regular_isRegular := C.isRegularKernel_modelMultiplier F hΘ hVU D.regular_isRegular g hg
    eq_off_diagonal := ?_ }⟩
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    have h := D.principal_degree u hu
    change u.degree - (d : ℤ) ≤ 2 - ((lam+d : ℕ) : ℤ)
    omega
  · intro ξ η hne
    rw [D.eq_off_diagonal ξ η hne, mul_add]
    congr 1
    simp only [terms, List.map_map, Function.comp_def,
      PrincipalTerm.multiplyHomogeneousModel_kernel, List.sum_map_mul_left]

end RothschildStein.P1

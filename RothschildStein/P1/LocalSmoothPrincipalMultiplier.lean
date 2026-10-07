-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LocalWeightedPrincipalType

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- A coefficient smooth jointly on the actual
endpoint patch preserves the type of a principal kernel. This handles
coefficient derivatives and the divergence terms in BB (11.36)–(11.37),
pp. 555–556, without requiring a global chart extension. -/
theorem LiftedChart.isTypeKernel_local_smooth_principal_multiplier
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (lam : ℕ) (hd : t.degree ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n+m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n+m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u)
    (a : ((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (C.U ×ˢ C.U)) :
    IsTypeKernel F lam (fun ξ η => a (ξ, η) * t.kernel ξ η) := by
  let T : Set ((((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ))) :=
    Prod.fst ⁻¹' (C.U ×ˢ C.U)
  have hT : IsOpen T := (C.isOpen_U.prod C.isOpen_U).preimage continuous_fst
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => a q.1) T :=
    ha.comp contDiffOn_fst (fun _ hq => hq)
  have ht := C.isTypeKernel_local_weighted_principal F hΘ hVU t 0 lam
    (by simpa using hd) hΓ hhom T hT (fun q => a q.1) hA
    (fun p hp => ⟨hVU (t.a.tsupport_subset hp.1), hVU (t.b.tsupport_subset hp.2)⟩)
    (fun _ hp => hp) (fun _ _ _ hI => False.elim (Nat.not_lt_zero _ hI))
  convert ht using 1
  funext ξ η
  simp only [PrincipalTerm.kernel, PrincipalTerm.modelKernel]
  ring

end RothschildStein.P1

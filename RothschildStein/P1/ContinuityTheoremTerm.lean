-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityTheoremPatch
public import RothschildStein.P1.ContinuitySingularFull
public import RothschildStein.P1.ContinuityRegularAssembly

/-!
# Continuity for one principal term

Every principal term `t = a(ξ) b(η) (D^{ξ,η} Γ_ε)(Θ(η, ξ))` of a type decomposition has
principal-value bounds on `V` (`LiftedChart.PVBounds`):

* degree `≤ 1` (positive type): the kernel is a patch kernel (`PrincipalTerm.patchKernel`), so its
  principal value is the absolutely convergent integral and the Schur and `C^α` bounds apply;
* degree `2` (type `0`): the kernel is the near part plus the far part
  (`principalTerm_kernel_eq_near_add_far`). The far part is a regular kernel (`farKernel_isRegular`),
  the near part has the Hölder and `L^p` bounds of H2 (Hölder continuity of `T(1)`, singular integrals on `C^δ`,
  and `L^p` bounds for singular integrals) on the doubled balls of the
  finite localization (`exists_nearTerm_holder_bound`, `exists_nearOutput_lp_bound`, with the Data D of
  finite localization, for the original splitting and for the separately constructed splitting of
  the transposed kernel).

The pole of the term is an arbitrary H1 fundamental kernel `Γ` of a standing hypothesis `H` of the
model with the shell cancellation `KernelShellCancellation Γ` (`F.pole t.star = Γ`); for `star = true`
this is the reflected kernel of the reversed-drift model (BB Thm 11.5(e)).
(BB pp. 299–301, 306–309, 325–327, 566–576.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **A principal term of degree `≤ 1` has principal-value bounds**: its kernel is a patch kernel. -/
theorem PVBounds.of_principalTerm_degree_le_one {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (hdeg : t.degree ≤ 1) :
    C.PVBounds H.norm (F.V : Set (Fin (n + m) → ℝ)) t.kernel :=
  PVBounds.of_patchKernel H.norm.gauge (PrincipalTerm.patchKernel hF t hdeg)

/-- **A degree-2 principal term has principal-value
bounds** (singular part: near part by H2 on the doubled balls of the finite localization, far part
regular). The pole of the term is an H1 fundamental kernel `Γ` of `H` with the shell cancellation. -/
theorem PVBounds.of_principalTerm_degree_two {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (hF : C.IsLiftedFrame F) (hQ : 2 < (C.G.homogeneousDimension : ℝ))
    (hsym : ∀ u, H.norm (-u) = H.norm u) (hνs : H.norm.Smooth)
    (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    (t : PrincipalTerm F) (hdeg : t.degree = 2) (hpole : F.pole t.star = ⇑Γ) :
    C.PVBounds H.norm (F.V : Set (Fin (n + m) → ℝ)) t.kernel := by
  have hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
  obtain ⟨cert, hfar, hker⟩ := exists_principalTerm_reconstruction (C := C) t hF.G_eq hdeg hF.Θ_eq
    hV hsym hνs Γ hpole
  have SF := t.toSplitFamily hF.G_eq hdeg
  have hc : C.IsTermCutoffs (F.V : Set (Fin (n + m) → ℝ)) (tsupport t.a) t.a t.b :=
    IsTermCutoffs.of_testFunction F.V hV t.a t.b
  obtain ⟨dd, -⟩ := exists_nearDataD hQ hsym hνs Γ hΓ SF cert
  have hnear : C.PVBounds H.norm (F.V : Set (Fin (n + m) → ℝ))
      (C.nearKernel H.norm t.D Γ cert.φ t.a t.b) := by
    refine ⟨fun {α} hα0 hα1 => ?_, fun {p} hp {α} hα0 hα1 => ?_⟩
    · exact exists_nearTerm_holder_bound hQ hsym hνs Γ hΓ SF cert hc hα0 hα1
    · obtain ⟨Λ, hΛ, hb⟩ := exists_nearOutput_lp_bound dd hc hp hα0 hα1
      obtain ⟨CH, -, hCH⟩ := exists_nearOutput_holder_bound dd H.norm.gauge hc hα0 hα1
      refine ⟨Λ, hΛ, fun f hf hfm => ?_⟩
      have heq : rhoPV (C.rhoGauge H.norm) (C.nearKernel H.norm t.D Γ cert.φ t.a t.b) f =
          nearOutput dd t.a t.b f := funext fun ξ => ((hCH f hf).1 ξ).rhoPV_eq
      rw [heq]
      exact hb f hf hfm
  have hfarPV : C.PVBounds H.norm (F.V : Set (Fin (n + m) → ℝ))
      (C.farKernel H.norm t.D Γ cert.φ t.a t.b) :=
    PVBounds.of_patchKernel H.norm.gauge ((hfar 1).patchKernel hF)
  exact (hnear.add hfarPV).congr_off_diagonal fun ξ η _ => (hker ξ η).symm

end LiftedChart

end RothschildStein.P1

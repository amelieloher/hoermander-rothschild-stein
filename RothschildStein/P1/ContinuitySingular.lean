-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuitySingularTests

/-!
# Singular integral and reconstruction estimates for degree `-Q` kernels

The statements for **one original degree-2 principal term**
`a(ξ) K(ξ, η) b(η)`, `K = (D^{ξ,η} Γ)(Θ(η, ξ))` (a `SplitFamily` `D` of degree-2 homogeneous
operators, `Γ` the H1 fundamental kernel with the shell cancellation `KernelShellCancellation`), on
the open patch `V ⊆ U`; the radial profile `φ` and the finite localization are those of the
`NearCertificate` (`exists_nearCertificate`), whose Data D certificates (original and separate
transpose, `exists_nearDataD`) are the premises of H2's Hölder continuity of `T(1)`, its singular integral bound on `C^δ`
and its `L^p` bound for singular integrals.

* **Reconstruction and extension**:
  - `principalTerm_kernel_eq_near_add_far`, `farKernel_isRegular`: the part outside the radial
    profile is a smooth compactly supported (regular) kernel;
  - `sum_cutoffKernel_eq`, `rhoTruncated_near_eq`, `hasRhoPV_near`: the finite reconstruction formula
    `T_near f = a ∑_j T_j (b f)`, for the kernel, the `ρ`-truncations and the principal value;
  - `localKernelData_principalValue_holder`: the zero extension of the local outputs preserves the
    Hölder bounds; `exists_boundedHolder_mul_extension`: the controlled Hölder extension of `b f`
    into the carrier (the margin `δ_b`);
* **Hölder bound of the near part**: `exists_nearTerm_holder_bound`;
* **`L^p` bound of the near part**: `exists_nearTerm_lpExtension_intrinsic`;
* **Agreement of the two realizations**: the last two conjuncts of the latter.

The far part of the term is a regular kernel (`farKernel_isRegular`); its bounds and its principal
value (an absolutely convergent integral) are those of a regular kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter TopologicalSpace
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}
variable {q : ℕ} {H : H1.StandingHypotheses C.G q}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
  {Fs V : Set (Fin (n + m) → ℝ)} {a b : (Fin (n + m) → ℝ) → ℝ}

/-- **Hölder continuity of one degree `-Q` term** (H2's Hölder continuity of `T(1)` and singular integral bound on
the doubled balls with the Data D, BB pp. 306-309, Prop 7.17 and Cor 7.19).
For `0 < α < 1` there is `C_H` such that for every `f` of finite Hölder norm on `V`
(lifted control distance `C.dl`) the `ρ`-principal value of the term's near part exists at every
point and `‖T_near f‖_{C^α(V)} ≤ C_H ‖f‖_{C^α(V)}`. -/
theorem exists_nearTerm_holder_bound (hQ : 2 < (C.G.homogeneousDimension : ℝ))
    (hsym : ∀ u, H.norm (-u) = H.norm u) (hνs : H.norm.Smooth) (Γ : H1.FundamentalKernel C.G H)
    (hΓ : H1.KernelShellCancellation Γ) (SF : SplitFamily C.G D)
    (cert : C.NearCertificate H.norm Fs) (hc : C.IsTermCutoffs V Fs a b) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α V f ≠ ⊤ →
      (∀ ξ, HasRhoPV (C.rhoGauge H.norm) (C.nearKernel H.norm D Γ cert.φ a b) f ξ
        (rhoPV (C.rhoGauge H.norm) (C.nearKernel H.norm D Γ cert.φ a b) f ξ)) ∧
      holderENorm C.dl α V (rhoPV (C.rhoGauge H.norm) (C.nearKernel H.norm D Γ cert.φ a b) f) ≤
        ENNReal.ofReal CH * holderENorm C.dl α V f := by
  obtain ⟨dd, -⟩ := exists_nearDataD hQ hsym hνs Γ hΓ SF cert
  obtain ⟨CH, hCH0, hCH⟩ := exists_nearOutput_holder_bound dd H.norm.gauge hc hα0 hα1
  refine ⟨CH, hCH0, fun f hf => ?_⟩
  obtain ⟨hpv, hb⟩ := hCH f hf
  have heq : rhoPV (C.rhoGauge H.norm) (C.nearKernel H.norm D Γ cert.φ a b) f =
      nearOutput dd a b f := funext fun ξ => (hpv ξ).rhoPV_eq
  rw [heq]
  exact ⟨hpv, hb⟩

end LiftedChart
end RothschildStein.P1

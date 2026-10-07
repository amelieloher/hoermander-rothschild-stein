-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuitySingular
public import RothschildStein.P1.ContinuityReconstructionIntegrable

/-!
# Reconstruction and extension for a principal term

The reconstruction for one principal term `t : PrincipalTerm F` of degree `2` of the kernel frame
`F` of a lifted chart:

* `exists_principalTerm_reconstruction`: there is a near certificate (radial profile `φ`, finite
  localization, symmetric truncation) for the output support `supp a` such that the term's kernel is
  the sum of the near part and of the far part, and the far part is a regular kernel of every
  budget (smooth, compactly supported in `V × V`);
* `hasRhoPV_fullKernel`: the `ρ`-principal value of the **whole** term exists, for every `f` of
  finite Hölder norm (every test), and is the principal value of the near part plus the absolutely
  convergent integral of the far part.
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

/-- The truncation distance of the frame is the gauge truncation `ρ = ν(Θ(η, ξ))` of the
chart when the frame has the chart's two-point map and the gauge `ν`. -/
theorem kernelFrame_rho_eq_rhoGauge {F : KernelFrame (n + m)} {ν : (Fin (n + m) → ℝ) → ℝ}
    (hΘ : F.Θ = C.Θ) (hg : F.gauge = ν) : F.rho = C.rhoGauge ν := by
  funext ξ η
  simp [KernelFrame.rho, rhoGauge, hΘ, hg]

/-- **Reconstruction for one principal term**
(the finite reconstruction formula; "its part outside the radial profile is a smooth, compactly
supported off-diagonal kernel, so it is regular"). For a degree-2 term `t` of a frame `F` with the
chart's two-point map, the cutoff region `V ⊆ U` and the pole `Γ`, there is a near certificate
(radial profile `φ`, truncation, finite localization of `supp a`) such that
`t.kernel = near part + far part` and the far part is `IsRegularKernel` for every budget. -/
theorem exists_principalTerm_reconstruction {F : KernelFrame (n + m)} (t : PrincipalTerm F)
    (hG : F.G = C.G) (hdeg : t.degree = 2) (hΘ : F.Θ = C.Θ)
    (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U) (hsym : ∀ u, H.norm (-u) = H.norm u)
    (hνs : H.norm.Smooth) (Γ : H1.FundamentalKernel C.G H) (hpole : F.pole t.star = ⇑Γ) :
    ∃ cert : C.NearCertificate H.norm (tsupport t.a),
      (∀ m' : ℕ, IsRegularKernel F m' (C.farKernel H.norm t.D Γ cert.φ t.a t.b)) ∧
      (∀ ξ η, t.kernel ξ η =
        C.nearKernel H.norm t.D Γ cert.φ t.a t.b ξ η +
          C.farKernel H.norm t.D Γ cert.φ t.a t.b ξ η) := by
  obtain ⟨cert⟩ := exists_nearCertificate (C := C) (Fs := tsupport t.a) t.a.hasCompactSupport
    (t.a.tsupport_subset.trans hV) H.norm.gauge hsym (τ := 1) one_pos
  refine ⟨cert, fun m' => ?_, fun ξ η => principalTerm_kernel_eq_near_add_far t hΘ hpole _ _ ξ η⟩
  exact farKernel_isRegular F hV H.norm.gauge hνs (t.toSplitFamily hG hdeg)
    Γ.smooth_off_zero cert.φ_smooth (ε := cert.R' / 2) (by linarith [cert.hR.pos])
    (fun u hu => cert.φ_one u hu) t.a t.b m'

variable {ν : (Fin (n + m) → ℝ) → ℝ} {Γ : (Fin (n + m) → ℝ) → ℝ} {cert : C.NearCertificate ν Fs}

end LiftedChart
end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SmoothFluxCoefficient
public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.P1.LiftedChart
public import RothschildStein.Definitions.testMultiplierOn

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RothschildStein.P1

/-- The principal family with parameter evaluated on the diagonal
has a smooth annular flux coefficient. -/
theorem PrincipalTerm.contDiff_endpointFluxCoefficient {N : ℕ} {F : KernelFrame N}
    (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (η : (Fin N → ℝ) → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ζ : Fin N → ℝ =>
      ∫ u, t.modelKernel ζ ζ u * fieldDerivative Y (fun v => 1 - η v) u) := by
  apply contDiff_exteriorFluxCoefficient
    (fun q : (Fin N → ℝ) × (Fin N → ℝ) => t.modelKernel q.1 q.1 q.2) _
    Y hY η hη hsη heη
  exact (t.modelKernel_contDiffOn hΓ).comp
    (contDiffOn_fst.prodMk (contDiffOn_fst.prodMk contDiffOn_snd)) (fun _ h => h)

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The precise positive-sign endpoint flux is
an actual compact smooth multiplier in V, including the chart density.
It is constructed from the singular principal family and a fixed annular
cutoff (BB Lemma 11.18, pp. 549–551). -/
def LiftedChart.endpointFluxMultiplier
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U) (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (Y : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (η : (Fin (n + m) → ℝ) → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (heη : η =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1) :
    TestFunction F.V ℝ (⊤ : ℕ∞) :=
  testMultiplierOn F.V
    (fun ζ => t.b ζ * C.c ζ *
      (∫ u, t.modelKernel ζ ζ u * fieldDerivative Y (fun v => 1 - η v) u))
    ((t.b.contDiff.contDiffOn.mul (C.density_smooth.mono hVU)).mul
      (t.contDiff_endpointFluxCoefficient hΓ Y hY η hη hsη heη).contDiffOn) t.a

/-- The constructed multiplier has exactly the
source coefficient a(ζ)b(ζ)c(ζ)∫g^ζ Yχ, with a positive sign. -/
theorem LiftedChart.endpointFluxMultiplier_apply
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U) (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (Y : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (η : (Fin (n + m) → ℝ) → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (heη : η =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ζ : Fin (n + m) → ℝ) :
    C.endpointFluxMultiplier F hVU t hΓ Y hY η hη hsη heη ζ =
      t.a ζ * t.b ζ * C.c ζ *
        (∫ u, t.modelKernel ζ ζ u * fieldDerivative Y (fun v => 1 - η v) u) := by
  change t.a ζ * (t.b ζ * C.c ζ * _) = _
  ring

end RothschildStein.P1

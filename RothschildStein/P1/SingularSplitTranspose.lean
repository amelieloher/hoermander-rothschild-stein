-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitCancellation
public import RothschildStein.P1.SingularSplitReflection

/-!
# The transpose has its own singular split

The transpose kernel `Kᵗ(ξ, η) = K(η, ξ) = k^{η,ξ}(Θ(ξ, η))` is rewritten, using the exact
antisymmetry `Θ(ξ, η) = -Θ(η, ξ)`, the symmetry of the gauge and the reflection
`(D Γ)(-u) = (D^refl Γ*)(u)` of BB (11.12), p. 546 (`differentialReflection_kernelSwap`), as the
kernel `k'^{ξ,η}(Θ(η, ξ))` of the *same shape* with the exchanged-and-reflected parameter family
`D'^{ξ,η} = refl(D^{η,ξ})` (`transposeFamily`) and the reflected pole `Γ*(u) = Γ(-u)`
(`FundamentalKernel.reflection`, BB Thm 11.5(e)). The singular split is then applied to this new
kernel, so `Kᵗ = K'₀ + K'₁` where `K'₀` is evaluated on its own diagonal and divided by its
own input density correction, and `K'₀` has its own annular cancellation (`integral_splitK0_annulus`
for the reflected data). Cancellation is not asserted for the raw `K₀ᵗ`. By symmetry of the gauge,
`ρ(ξ, η) = ρ(η, ξ)` (`rhoGauge_comm`), so the transposed truncation region is the same annulus.
(BB p. 576, Prop 11.33(d).)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- The transposed parameter family: exchange the two parameters and
reflect the operator, `D'^{ξ,η} = refl(D^{η,ξ})` (BB (11.12), p. 546). -/
def transposeFamily {N : ℕ}
    (D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N) :
    (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N :=
  fun ξ η => differentialReflection (D η ξ)

/-- The transposed family is homogeneous of the same degree as the original one
(`differentialReflection_homogeneous`). -/
theorem transposeFamily_isHomogeneous {N : ℕ} {G : HomogeneousGroup N}
    {D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N} {β : ℝ}
    (hD : ∀ ξ η, (D ξ η).IsHomogeneous G β) (ξ η : Fin N → ℝ) :
    (transposeFamily D ξ η).IsHomogeneous G β :=
  differentialReflection_homogeneous G (D η ξ) (hD η ξ)

/-- The coefficients of the transposed family are jointly smooth in `(ξ, η, u)` when
those of the original family are. -/
theorem transposeFamily_coefficient_smooth {N : ℕ}
    {D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N} (α : Fin N → ℕ)
    (h : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) => (D z.1 z.2.1).coefficient α z.2.2)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) =>
        (transposeFamily D z.1 z.2.1).coefficient α z.2.2) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) => (z.2.1, z.1, -z.2.2)) :=
    contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd.neg)
  have := contDiff_const (c := ((-1 : ℝ) ^ (∑ j, α j))).mul (h.comp hg)
  exact this

/-- The transposed family has the same degree and, for a common index set, the same
index set. -/
theorem transposeFamily_indices_eq {N : ℕ}
    {D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N} {I : Finset (Fin N → ℕ)}
    (hI : ∀ ξ η, (D ξ η).indices = I) (ξ η : Fin N → ℝ) :
    (transposeFamily D ξ η).indices = I := hI η ξ

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The lifted-chart inversion field `inv_eq_neg` in the form `G.inv u = -u`. -/
theorem G_inv_eq_neg (u : Fin (n + m) → ℝ) : C.G.inv u = -u := C.inv_eq_neg u

/-- `Θ(η, ξ) ≠ 0` off the diagonal of `U × U` (injectivity of the chart `e ξ`). -/
theorem Θ_ne_zero_of_ne {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : η ≠ ξ) :
    C.Θ η ξ ≠ 0 := by
  intro h
  apply hne
  have h0 : C.Θ ξ ξ = 0 := (C.chart ξ hξ).2.2.2.2
  exact C.injOn_Θ_fst hξ hη hξ (h.trans h0.symm)

/-- Endpoint exchange and reflection: for a symmetric gauge and a
pole `Γs` with `Γs u = Γ(-u)` off zero, the transpose of the cut-off kernel is the cut-off kernel
of the transposed family with the reflected pole,
`K(η, ξ) = K'(ξ, η)` where `K'^{ξ,η}(u) = (refl D^{η,ξ} Γs)(u) φ(ν u)` (BB p. 576). -/
theorem pairKernel_transpose {ν : (Fin (n + m) → ℝ) → ℝ} (hν : ∀ u, ν (-u) = ν u)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    {Γ Γs : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ}
    (hstar : ∀ u, u ≠ 0 → Γs u = Γ (-u))
    (hreg : ∀ ξ η, ∀ a ∈ (D ξ η).indices, ContDiffOn ℝ (∑ j, a j : ℕ) Γs {(0 : Fin (n + m) → ℝ)}ᶜ)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hu : C.Θ η ξ ≠ 0) :
    C.pairKernel ν D Γ φ η ξ = C.pairKernel ν (transposeFamily D) Γs φ ξ η := by
  unfold pairKernel cutoffKernel transposeFamily
  rw [C.theta_antisymm η hη ξ hξ, hν, differentialReflection_kernelSwap (D η ξ) hstar (hreg η ξ) hu]

/-- The transpose kernel has its own splitting: off the diagonal of
`U × U`, `K(η, ξ) = K'₀(ξ, η) + K'₁(ξ, η)`, where `K'₀, K'₁` are the singular-split pieces of the
exchanged-and-reflected data `(transposeFamily D, Γs)` (BB p. 576, Prop 11.33(d)). -/
theorem pairKernel_transpose_eq_split {ν : (Fin (n + m) → ℝ) → ℝ} (hν : ∀ u, ν (-u) = ν u)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    {Γ Γs : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ}
    (hstar : ∀ u, u ≠ 0 → Γs u = Γ (-u))
    (hreg : ∀ ξ η, ∀ a ∈ (D ξ η).indices, ContDiffOn ℝ (∑ j, a j : ℕ) Γs {(0 : Fin (n + m) → ℝ)}ᶜ)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : η ≠ ξ) :
    C.pairKernel ν D Γ φ η ξ =
      C.splitK0 ν (transposeFamily D) Γs φ ξ η + C.splitK1 ν (transposeFamily D) Γs φ ξ η :=
  (C.pairKernel_transpose hν hstar hreg hξ hη (C.Θ_ne_zero_of_ne hξ hη hne)).trans
    (pairKernel_eq_splitK0_add_splitK1 hξ hη)

/-- The transpose splitting for the fundamental kernel of H1:
the pole of the transposed data is the reflected kernel `Γ* = Γ.reflection hQ`
(BB Thm 11.5(e), `Γ*(u) = Γ(-u)`), a fundamental kernel for the drift-reversed standing hypotheses. -/
theorem pairKernel_transpose_eq_split_reflection {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (Γ : H1.FundamentalKernel C.G H) (hQ : 2 < (C.G.homogeneousDimension : ℝ))
    (hsym : ∀ u, H.norm (-u) = H.norm u)
    (D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)) (φ : ℝ → ℝ)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : η ≠ ξ) :
    C.pairKernel H.norm D Γ φ η ξ =
      C.splitK0 H.norm (transposeFamily D) (Γ.reflection hQ) φ ξ η +
        C.splitK1 H.norm (transposeFamily D) (Γ.reflection hQ) φ ξ η :=
  C.pairKernel_transpose_eq_split hsym
    (fun u _ => Γ.reflection_neg hQ C.G_inv_eq_neg u)
    (fun _ _ a _ => (Γ.reflection hQ).smooth_off_zero.of_le (by exact_mod_cast le_top))
    hξ hη hne

end LiftedChart
end RothschildStein.P1

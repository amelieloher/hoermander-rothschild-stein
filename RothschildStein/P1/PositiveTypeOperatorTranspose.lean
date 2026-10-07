-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PositiveTypeTransposePairing
public import RothschildStein.P1.ChartTranspose

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- An actual positive-type operator has a same-type transpose
with the swapped kernel, the identical multiplier, and the bilinear
pairing identity on all compactly supported smooth tests. -/
theorem LiftedChart.exists_positiveType_transpose
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hG : F.G = C.G) (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓs : ∀ u : Fin (n + m) → ℝ, u ≠ 0 → F.Γs u = F.Γ (-u))
    (hΓ : ∀ star : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ star : Bool, ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (lam : ℕ) (hlam : 1 ≤ lam) (T : TypeOperator F lam) :
    ∃ S : TypeOperator F lam,
      S.kernel = (fun ξ η => T.kernel η ξ) ∧ S.mult = T.mult ∧
      ∀ f g : TestFunction F.V ℝ (⊤ : ℕ∞),
        (∫ ξ, g ξ * T.apply f ξ) = ∫ η, f η * S.apply g η := by
  let S : TypeOperator F lam := {
    kernel := fun ξ η => T.kernel η ξ
    isType := C.isTypeKernel_transpose F hΘ hVU hΓs (hΓ false) (hΓ true) lam T.kernel T.isType
    mult := T.mult
    mult_eq_zero := T.mult_eq_zero }
  refine ⟨S, rfl, rfl, ?_⟩
  intro f g
  have h0 : lam ≠ 0 := by omega
  simp only [TypeOperator.apply, ite_eq_right h0]
  exact C.positiveType_bilinearTranspose F hG hΘ hVU hΓ hhom lam hlam T.kernel T.isType
    f g f.contDiff.continuous.measurable
    (f.contDiff.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    g.contDiff.continuous.measurable g.memLp_top

end RothschildStein.P1

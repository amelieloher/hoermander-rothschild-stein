-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitCancellation
public import RothschildStein.P1.ModelHypotheses
public import RothschildStein.G2.InvariantBracket
public import RothschildStein.G2.InversionFields
public import RothschildStein.G2.LeftRightBasisChange

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Every model bracket is left invariant. -/
theorem modelWord_isLeftInvariant (I : List (Fin k)) :
    G2.IsLeftInvariantField C.G (wordBracket C.Y I) := by
  induction I with
  | nil =>
    intro u z
    simp only [wordBracket, Pi.zero_apply, map_zero]
  | cons i I ih =>
    cases I with
    | nil => exact C.isLeftInvariantField i
    | cons j J => exact (C.isLeftInvariantField i).lieBracket C.G ih

/-- The model bracket basis is the canonical left invariant basis. -/
theorem modelBasis_eq_leftField (j : Fin (n + m)) :
    wordBracket C.Y (C.B j) = G2.leftField C.G (Pi.single j 1) := by
  rw [(C.modelWord_isLeftInvariant (C.B j)).eq_leftField C.G, C.model_basis_origin j]

/-- Input-endpoint differentiation uses the reflected model
bracket and the entire reflected remainder, including lower coordinates. -/
theorem inputBracket_approx (I : List (Fin k)) (hI : I ≠ [])
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    fderiv ℝ (fun ζ => C.Θ ζ ξ) η (wordBracket C.Xl I η) =
      -wordBracket C.Y I (-C.Θ η ξ) - C.R I ξ (-C.Θ η ξ) := by
  have he : (fun ζ => C.Θ ζ ξ) =ᶠ[𝓝 η] (fun ζ => -C.Θ ξ ζ) := by
    filter_upwards [C.isOpen_U.mem_nhds hη] with ζ hζ
    exact C.theta_antisymm ξ hξ ζ hζ
  rw [he.fderiv_eq, fderiv_fun_neg, neg_apply,
    C.bracket_approx I hI ξ hξ η hη, C.theta_antisymm η hη ξ hξ]
  exact neg_add _ _

/-- Input differentiation by a basis bracket is the negative
canonical right invariant field plus the full reflected remainder. -/
theorem inputBasis_approx (j : Fin (n + m))
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    fderiv ℝ (fun ζ => C.Θ ζ ξ) η (wordBracket C.Xl (C.B j) η) =
      -G2.rightField C.G (Pi.single j 1) (C.Θ η ξ) - C.R (C.B j) ξ (-C.Θ η ξ) := by
  rw [C.inputBracket_approx (C.B j) (C.basis_weight j).1 hξ hη,
    C.modelBasis_eq_leftField]
  have hi : C.G.inv = fun u : Fin (n + m) → ℝ => -u := funext C.inv_eq_neg
  have hd := G2.inv_fderiv_leftField C.G (Pi.single j 1) (-C.Θ η ξ)
  rw [hi, fderiv_fun_neg] at hd
  simp only [fderiv_fun_id, neg_apply, ContinuousLinearMap.id_apply, neg_neg] at hd
  rw [neg_inj.mp hd]

end RothschildStein.P1.LiftedChart

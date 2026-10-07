-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import Hormander.Interface.BasisVec
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.controlDistance
public import RothschildStein.Definitions.WordCoefficients
public import RothschildStein.Definitions.truncatedBracket
public import RothschildStein.Definitions.formalSpan
public import RothschildStein.Definitions.freeDimension
public import RothschildStein.Definitions.FreeAt
public import RothschildStein.Definitions.StepSpansAt
public import RothschildStein.Definitions.WeightedJet
public import RothschildStein.Definitions.rsBall
public import RothschildStein.Definitions.basePoint
public import RothschildStein.Definitions.joinPoint
public import RothschildStein.Definitions.triangularLift
public import RothschildStein.Definitions.absoluteJacobian
public import RothschildStein.Definitions.rsGauge
public import RothschildStein.Definitions.fiberVolume
public import RothschildStein.Definitions.HomogeneousGroup
public import RothschildStein.Definitions.coordinateDilation
public import RothschildStein.Definitions.polynomialProduct
public import RothschildStein.Definitions.HomogeneousGroup.mul
public import RothschildStein.Definitions.HomogeneousGroup.dilate
public import RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension

/-!
# The lifted chart consumed by P1 and P2

`LiftedChart w s Ω hΩ X x₀ m` holds, as named fields, exactly the data and the conjuncts of the
conclusion of the lifting theorems `RothschildStein.exists_lift_approximation_noDrift`
(alphabet `Fin q`, all weights one) and `RothschildStein.exists_lift_approximation_drift`
(alphabet `Fin (q + 1)`, weight two at the drift letter `0`), for a general alphabet `Fin k`
and weights `w`. The model dilation exponent is written `-(w i)`; the two lifting theorems
spell it `-1` and `if i = 0 then -2 else -1`. The conversions from those statements are in
`RothschildStein.P1.LiftedChartOfRS1`.

This is the lifted-chart interface used by P1 and P2; no field goes beyond the conclusion of the
lifting theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal CompactConvergenceCLM
namespace RothschildStein.P1

/-- The lifted chart at `x₀`: the free triangular lift, the homogeneous
model group and its fields, the two-point map `Θ`, the remainders, the endpoint densities, the
gauge comparison, fiber averaging and the uniform ball/fiber volume bounds. The fields are the
conjuncts of the conclusion of the lifting theorem, in order (BB pp. 483–485, 509–517, 584–585). -/
structure LiftedChart {n k : ℕ} (w : Fin k → ℕ+) (s : ℕ) (Ω : Set (Fin n → ℝ))
    (hΩ : IsOpen Ω) (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (m : ℕ) where
  /-- The lift polynomials. -/
  P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ
  /-- The lifted coordinate neighborhood. -/
  U : Set (Fin (n + m) → ℝ)
  /-- The homogeneous model group. -/
  G : HomogeneousGroup (n + m)
  /-- The model bracket basis. -/
  B : Fin (n + m) → List (Fin k)
  /-- Coordinates of the generators in the bracket basis. -/
  v : Fin k → (Fin (n + m) → ℝ)
  /-- The left invariant model fields. -/
  Y : Fin k → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)
  /-- The two-point map, `Θ η ξ`. -/
  Θ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)
  /-- The endpoint charts `ξ ↦ Θ η ξ`. -/
  e : (Fin (n + m) → ℝ) → OpenPartialHomeomorph (Fin (n + m) → ℝ) (Fin (n + m) → ℝ)
  /-- The bracket remainders. -/
  R : List (Fin k) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)
  /-- The density factor. -/
  c : (Fin (n + m) → ℝ) → ℝ
  /-- The output-variable density correction. -/
  ωp : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ
  /-- The input-variable density correction. -/
  ωm : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ
  vars_lt : ∀ i l, ∀ j ∈ (P i l).vars, j.val < n + l.val
  isOpen_U : IsOpen U
  isCompact_closure_U : IsCompact (closure U)
  closure_U_subset : closure U ⊆ {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω}
  center_mem : joinPoint x₀ (0 : Fin m → ℝ) ∈ U
  lift_smooth : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i)
    {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω}
  lift_free : ∀ ξ ∈ U, FreeAt w s (triangularLift X P) ξ ∧ StepSpansAt w s (triangularLift X P) ξ
  basis_weight : ∀ j, B j ≠ [] ∧ wordWeight w (B j) ≤ s ∧ G.weight j = wordWeight w (B j)
  basis_independent : LinearIndependent ℝ
    (fun j => (truncatedBracket (B j) : WordCoefficients k s w))
  basis_span : Submodule.span ℝ (Set.range (fun j =>
    (truncatedBracket (B j) : WordCoefficients k s w))) = formalSpan k s w
  generator_coords : ∀ i, (∑ j, v i j • (truncatedBracket (B j) : WordCoefficients k s w)) =
    truncatedBracket [i]
  inv_eq_neg : ∀ u, (fun j => MvPolynomial.eval u (G.inversePolynomial j)) = -u
  model_field_eq : ∀ i u, Y i u = fderiv ℝ (G.mul u) 0 (v i)
  model_field_smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i)
  model_field_invariant : ∀ i u z, fderiv ℝ (G.mul u) z (Y i z) = Y i (G.mul u z)
  model_field_homogeneous : ∀ i t, 0 < t → ∀ u,
    Y i (G.dilate t u) = t ^ (-((w i : ℕ) : ℤ)) • G.dilate t (Y i u)
  model_free : ∀ u, FreeAt w s Y u ∧ StepSpansAt w s Y u
  model_nilpotent : ∀ I : List (Fin k), s < wordWeight w I → wordBracket Y I = 0
  model_basis_origin : ∀ j, wordBracket Y (B j) 0 = Pi.single j 1
  model_exponential : ∀ u, (∑ j, u j • wordBracket Y (B j) u) = u
  theta_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Θ z.1 z.2) (U ×ˢ U)
  chart : ∀ η ∈ U, (e η).source = U ∧
    (∀ ξ ∈ U, e η ξ = Θ η ξ) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (e η) (e η).source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (e η).symm (e η).target ∧ Θ η η = 0
  radial_curve : ∀ η ∈ U, ∀ u ∈ (e η).target,
    ∃ γ : ℝ → (Fin (n + m) → ℝ), γ 0 = η ∧ γ 1 = (e η).symm u ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} ∧
        HasDerivAt γ (∑ j, u j • wordBracket (triangularLift X P) (B j) (γ t)) t)
  theta_antisymm : ∀ η ∈ U, ∀ ξ ∈ U, Θ ξ η = -Θ η ξ
  isOpen_T : IsOpen {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) |
    z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  remainder_smooth : ∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => R I z.1 z.2)
    {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  remainder_weight : ∀ I, I ≠ [] → ∀ η ∈ U,
    WeightedJet G.weight (1 - (wordWeight w I : ℤ)) (R I η)
  remainder_origin : ∀ I, I ≠ [] → wordWeight w I ≤ s → ∀ η ∈ U, R I η 0 = 0
  bracket_approx : ∀ I, I ≠ [] → ∀ η ∈ U, ∀ ξ ∈ U,
    fderiv ℝ (Θ η) ξ (wordBracket (triangularLift X P) I ξ) =
      wordBracket Y I (Θ η ξ) + R I η (Θ η ξ)
  density_smooth : ContDiffOn ℝ (⊤ : ℕ∞) c U
  density_pos : ∀ η ∈ U, 0 < c η
  ωp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωp z.1 z.2)
    {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  ωm_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωm z.1 z.2)
    {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  ω_origin : ∀ η ∈ U, ωp η 0 = 0 ∧ ωm η 0 = 0
  ωm_eq : ∀ η ∈ U, ∀ u, ωm η u = ωp η (-u)
  jacobian : ∀ η ∈ U, ∀ ξ ∈ U,
    0 < 1 + ωp η (Θ η ξ) ∧ 0 < 1 + ωm ξ (Θ η ξ) ∧
    absoluteJacobian (Θ η) ξ = (c η * (1 + ωp η (Θ η ξ)))⁻¹ ∧
    absoluteJacobian (fun ζ => Θ ζ ξ) η = (c ξ * (1 + ωm ξ (Θ η ξ)))⁻¹
  density_bounds : ∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
    ∃ cmin cmax C r : ℝ, 0 < cmin ∧ 0 < cmax ∧ 0 < C ∧ 0 < r ∧
      (∀ η ∈ K, cmin ≤ c η ∧ c η ≤ cmax) ∧
      (∀ η ∈ K, ∀ u ∈ (e η).target, ‖u‖ < r →
        |ωp η u| ≤ C * ‖u‖ ∧ |ωm η u| ≤ C * ‖u‖)
  gauge_comparison : ∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ η ∈ U, ∀ ξ ∈ U,
    ENNReal.ofReal (rsGauge G.weight G.weight_pos (Θ η ξ) / Cρ) ≤
      controlDistance {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X P) η ξ ∧
    controlDistance {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X P) η ξ ≤
      ENNReal.ofReal (Cρ * rsGauge G.weight G.weight_pos (Θ η ξ))
  fiber_average : ∀ V : TopologicalSpace.Opens (Fin (n + m) → ℝ), (V : Set _) = U →
    ∃ F : TestFunction V ℝ (⊤ : ℕ∞) →L_c[ℝ]
      TestFunction (⟨Ω, hΩ⟩ : TopologicalSpace.Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞),
      ∀ φ x, F φ x = ∫ t : Fin m → ℝ, φ (joinPoint x t)
  ball_bounds : ∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
    ∃ rstar cv Cv δ cf Cf : ℝ,
      0 < rstar ∧ 0 < cv ∧ 0 < Cv ∧ 0 < δ ∧ δ < 1 ∧ 0 < cf ∧ 0 < Cf ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
        let Ul := rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X P) η r
        let Vb := rsBall Ω w X (basePoint η) r
        Ul ⊆ U ∧ MeasurableSet Ul ∧ MeasurableSet Vb ∧
        volume Ul ≠ ⊤ ∧ volume Vb ≠ ⊤ ∧
        0 < (volume Ul).toReal ∧ 0 < (volume Vb).toReal ∧
        cv * r ^ G.homogeneousDimension ≤ (volume Ul).toReal ∧
        (volume Ul).toReal ≤ Cv * r ^ G.homogeneousDimension ∧
        (∀ ξ ∈ Ul, controlDistance Ω w X (basePoint η) (basePoint ξ) ≤
          controlDistance {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X P) η ξ) ∧
        (∀ z : Fin n → ℝ,
          fiberVolume Ul z ≤ ENNReal.ofReal (Cf * (volume Ul).toReal / (volume Vb).toReal)) ∧
        (∀ z ∈ rsBall Ω w X (basePoint η) (δ * r),
          ENNReal.ofReal (cf * (volume Ul).toReal / (volume Vb).toReal) ≤ fiberVolume Ul z)

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The lifted fields `X̃ = triangularLift X P`. -/
abbrev Xl (C : LiftedChart w s Ω hΩ X x₀ m) : Fin k → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) :=
  triangularLift X C.P

/-- The lifted domain `O = {ξ | π ξ ∈ Ω}`. -/
abbrev O (_C : LiftedChart w s Ω hΩ X x₀ m) : Set (Fin (n + m) → ℝ) :=
  {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω}

/-- The domain `T` of the remainders and density corrections. -/
abbrev T (C : LiftedChart w s Ω hΩ X x₀ m) : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) :=
  {z | z.1 ∈ C.U ∧ z.2 ∈ (C.e z.1).target}

/-- The lifted control distance `d̃` on `O`. -/
abbrev dl (C : LiftedChart w s Ω hΩ X x₀ m) : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ≥0∞ :=
  controlDistance C.O w C.Xl

end LiftedChart

end RothschildStein.P1

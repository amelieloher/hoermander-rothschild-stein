-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib
public import HeatKernel.Statements.exists_heatKernel_gaussian
import HeatKernel.Statements.horizontal_poincare
import HeatKernel.Statements.parabolic_harnack
import HeatKernel.Statements.parabolic_holder
import HeatKernel.Statements.elliptic_harnack

/-!
# Solution: heat kernel, Poincaré and Harnack inequalities on Carnot groups, proved

This file repeats `Challenge.lean` verbatim and proves each of its theorems from the corresponding
theorem in `HeatKernel.Statements`. The definitions below are definitional copies of the
library's; the bridge maps the structure `HomogeneousGroup` to the library's copy.

The Challenge statement follows.

## Heat kernel, Poincaré and Harnack inequalities on Carnot groups

A standalone, Mathlib-only statement of the Gaussian heat-kernel bounds for the sub-Laplacian of a
Carnot group and of the Poincaré, Harnack and Hölder estimates on the way. Space is
`ℝᴺ = Fin N → ℝ` with Lebesgue measure; vector fields act by `Xf(x) = Df(x)·X(x)`. The group `G`
is a homogeneous group in polynomial coordinates (as in M. Bramanti and L. Brandolini, *Hörmander
Operators* (2023), cited as BB, Chapter 3) whose first `q` canonical left-invariant fields
`X₁, …, X_q` have weight one and are bracket-generating; `Q` is its homogeneous dimension.
Distances and balls are those of the horizontal `ℓ²`-control distance `d = horizontalL2Distance X`.

* `exists_heatKernel_gaussian` (L. Saloff-Coste, Int. Math. Res. Not. 1992; upper bound:
  D. Jerison and A. Sánchez-Calle, Indiana Univ. Math. J. 35 (1986)). There is a kernel
  `p(t, x, y)`, smooth on `(0, ∞) × G × G`, with
  `∂ₜp = Σ Xᵢ² p` in `x`, symmetric, satisfying Chapman–Kolmogorov, of unit mass, with initial
  value `δ_x` against bounded continuous functions, left-invariant, with
  `p(r²t, δ_r x, δ_r y) = r^{-Q} p(t, x, y)`, and with the two-sided Gaussian bounds
  `c t^{-Q/2} exp(-C d(x, y)²/t) ≤ p(t, x, y) ≤ C t^{-Q/2} exp(-c d(x, y)²/t)`.
* `horizontal_poincare` (D. Jerison, Duke Math. J. 53 (1986)). For `1 ≤ p < ∞`, on every ball
  `B = B(x, r)`, `(⨍_B |u - u_B|ᵖ)^{1/p} ≤ C r (⨍_B |Xu|ᵖ)^{1/p}` for `u` of class `C¹` near `B̄`.
* `parabolic_harnack`, `parabolic_holder`, `elliptic_harnack` (L. Saloff-Coste, Int. Math. Res.
  Not. 1992; A. Grigor'yan, Math. USSR Sb. 72 (1992); K.-T. Sturm, J. Math. Pures Appl. 75
  (1996)). For measurable symmetric coefficients `a` with `λ|ξ|² ≤ ξᵀaξ ≤ Λ|ξ|²`, nonnegative
  local weak solutions of `∂ₜu = Σᵢⱼ Xᵢ(aᵢⱼ Xⱼ u)` satisfy the parabolic Harnack inequality, every
  local weak solution has a continuous version on the inner cylinder with a Hölder bound for the
  parabolic distance `d(x, y) + |t - s|^{1/2}` in terms of its bounds on the outer cylinder,
  and nonnegative weak solutions of `Σᵢⱼ Xᵢ(aᵢⱼ Xⱼ u) = 0` satisfy the elliptic Harnack inequality.

All constants depend only on the group, its horizontal fields, `p` and `λ, Λ`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped Topology ENNReal

namespace HeatKernelChallenge

/-! ## Words, brackets and weights -/

/-- The right-nested bracket `[X_{i₁}, [X_{i₂}, …, X_{iⱼ}]]` of a nonempty word (`0` for `[]`). -/
def wordBracket {m n : ℕ} (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) :
    List (Fin m) → ((Fin n → ℝ) → (Fin n → ℝ))
  | [] => 0
  | [i] => X i
  | i :: j :: I => VectorField.lieBracket ℝ (X i) (wordBracket X (j :: I))

/-- Hörmander's condition for `X₁, …, X_m`: brackets of nonempty words span `ℝⁿ` on `Ω`. -/
def bracketSpansOn {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ x ∈ Ω, Submodule.span ℝ {v | ∃ I : List (Fin m), I ≠ [] ∧ v = wordBracket X I x} = ⊤

/-- The weight `Σⱼ w(iⱼ)` of a word. -/
def wordWeight {m : ℕ} (w : Fin m → ℕ+) (I : List (Fin m)) : ℕ :=
  (I.map fun i => (w i : ℕ)).sum

/-- All words (including the empty one) of weight at most `k`. -/
def wordFamily {m : ℕ} (w : Fin m → ℕ+) (k : ℕ) : Finset (List (Fin m)) := by
  classical
  exact ((Finset.range (k + 1)).biUnion fun l =>
    (Finset.univ : Finset (Fin l → Fin m)).image List.ofFn).filter
      (fun I => wordWeight w I ≤ k)

/-- Weights without drift: every field has weight one. -/
def noDriftWeight {q : ℕ} (_i : Fin q) : ℕ+ := 1

/-! ## Derivatives along fields and weak derivatives -/

/-- The derivative `Vf(x) = Df(x)·V(x)`. -/
def fieldDerivative {n : ℕ} (V : (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (V x)

/-- `Σᵢ Xᵢ² f`. -/
def sumSquares {q n : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, fieldDerivative (X i) (fieldDerivative (X i) f) x

/-- The Euclidean divergence `Σᵢ ∂ᵢVᵢ` of a vector field. -/
def euclideanDivergence {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (fderiv ℝ V x (Pi.single i 1)) i

/-- The formal transpose `Xᵀφ = -div(φX)` of a vector field. -/
def fieldTranspose {n : ℕ} (V : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  -euclideanDivergence (fun y => φ y • V y) x

/-- The transpose `(X_{i₁} ⋯ X_{iⱼ})ᵀφ = X_{iⱼ}ᵀ ⋯ X_{i₁}ᵀ φ` of a word. -/
def wordTranspose {m n : ℕ} (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) :
    List (Fin m) → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ)
  | [], φ => φ
  | i :: I, φ => wordTranspose X I (fieldTranspose (X i) φ)

/-- `g ∈ L¹_loc(V)` is the weak derivative `X_{i₁} ⋯ X_{iⱼ} f` on `V`. -/
def hasWeakWordDeriv {m n : ℕ} (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (I : List (Fin m)) (f g : (Fin n → ℝ) → ℝ) : Prop :=
  LocallyIntegrableOn f (V : Set (Fin n → ℝ)) volume ∧
  LocallyIntegrableOn g (V : Set (Fin n → ℝ)) volume ∧
  ∀ φ : TestFunction V ℝ (⊤ : ℕ∞),
    (∫ x in (V : Set (Fin n → ℝ)), g x * φ x) =
    ∫ x in (V : Set (Fin n → ℝ)), f x * wordTranspose X I φ x

/-- `f ∈ W^{k,p}_X(V)`: `f` and its weak derivatives along words of weight `≤ k` lie in `Lᵖ(V)`. -/
def memSobolevX {m n : ℕ} (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ) : Prop :=
  MemLp f p (volume.restrict (V : Set (Fin n → ℝ))) ∧
  ∀ I ∈ wordFamily w k, ∃ g : (Fin n → ℝ) → ℝ,
    hasWeakWordDeriv X V I f g ∧ MemLp g p (volume.restrict (V : Set (Fin n → ℝ)))

/-- `f ∈ W^{k,p}_{X,loc}(Ω)`: `f ∈ W^{k,p}_X(V)` for every open `V ⋐ Ω`. -/
def memSobolevXLoc {m n : ℕ} (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ V : Opens (Fin n → ℝ), IsCompact (closure (V : Set (Fin n → ℝ))) →
    closure (V : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) → memSobolevX w X V k p f

/-! ## Homogeneous groups -/

/-- The polynomial map `(x, y) ↦ (P_j(x, y))_j`. -/
def polynomialProduct {N : ℕ} (P : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℝ)
    (x y : Fin N → ℝ) : Fin N → ℝ :=
  fun j => MvPolynomial.eval (Sum.elim x y) (P j)

/-- The dilation `(t^{ω_j} x_j)_j`. -/
def coordinateDilation {N : ℕ} (w : Fin N → ℕ) (t : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun j => t ^ w j * x j

/-- A homogeneous group on `ℝᴺ` (BB Chapter 3): a polynomial group law with identity `0` and
polynomial inverse, for which the dilations with positive nondecreasing integer weights are
group automorphisms. -/
structure HomogeneousGroup (N : ℕ) where
  dimension_pos : 0 < N
  weight : Fin N → ℕ
  weight_pos : ∀ j, 0 < weight j
  weight_mono : Monotone weight
  productPolynomial : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℝ
  inversePolynomial : Fin N → MvPolynomial (Fin N) ℝ
  zero_left : ∀ x, polynomialProduct productPolynomial 0 x = x
  zero_right : ∀ x, polynomialProduct productPolynomial x 0 = x
  assoc : ∀ x y z,
    polynomialProduct productPolynomial (polynomialProduct productPolynomial x y) z =
      polynomialProduct productPolynomial x (polynomialProduct productPolynomial y z)
  inverse_left : ∀ x,
    polynomialProduct productPolynomial
      (fun j => MvPolynomial.eval x (inversePolynomial j)) x = 0
  inverse_right : ∀ x,
    polynomialProduct productPolynomial x
      (fun j => MvPolynomial.eval x (inversePolynomial j)) = 0
  dilation_product : ∀ t : ℝ, 0 < t → ∀ x y,
    coordinateDilation weight t (polynomialProduct productPolynomial x y) =
      polynomialProduct productPolynomial
        (coordinateDilation weight t x) (coordinateDilation weight t y)

namespace HomogeneousGroup

variable {N : ℕ} (G : HomogeneousGroup N)

/-- The group law `x ∘ y`. -/
def mul (x y : Fin N → ℝ) : Fin N → ℝ := polynomialProduct G.productPolynomial x y

/-- The group dilation `D(t)`. -/
def dilate (t : ℝ) (x : Fin N → ℝ) : Fin N → ℝ := coordinateDilation G.weight t x

/-- The homogeneous dimension `Q = Σⱼ ωⱼ`. -/
def homogeneousDimension : ℕ := ∑ j, G.weight j

/-- The left-invariant field `Zⱼ` equal to `∂ⱼ` at `0`: `Zⱼ(x) = D(y ↦ x ∘ y)(0) eⱼ`. -/
def canonicalField (j : Fin N) (x : Fin N → ℝ) : Fin N → ℝ :=
  fderiv ℝ (G.mul x) 0 (Pi.single j 1)

/-- The first `q` canonical fields `Z₁, …, Z_q`. -/
def horizontalFields {q : ℕ} (hq : q ≤ N) (i : Fin q) : (Fin N → ℝ) → (Fin N → ℝ) :=
  G.canonicalField (Fin.castLE hq i)

end HomogeneousGroup

namespace Bridge

/-- The library copy of a homogeneous group. -/
def HomogeneousGroup.toLib {N : ℕ} (G : HomogeneousGroup N) : RothschildStein.HomogeneousGroup N :=
  ⟨G.dimension_pos, G.weight, G.weight_pos, G.weight_mono, G.productPolynomial,
    G.inversePolynomial, G.zero_left, G.zero_right, G.assoc, G.inverse_left, G.inverse_right,
    G.dilation_product⟩

end Bridge

/-! ## The horizontal distance and local weak solutions -/

/-- The horizontal `ℓ²`-control distance of the fields `X₁, …, X_q`: the infimum, in `[0, ∞]`, of
the lengths `∫₀¹ |a(t)|₂ dt` of horizontal competitors from `x` to `y`, that is, absolutely
continuous curves `γ : [0, 1] → ℝᴺ` with `γ 0 = x`, `γ 1 = y` and `γ' = ∑ᵢ aᵢ Xᵢ(γ)` almost
everywhere, for almost-everywhere measurable controls `a` with integrable Euclidean norm. It is `∞`
when there is no competitor. -/
def horizontalL2Distance {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (x y : Fin N → ℝ) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ (γ : ℝ → (Fin N → ℝ)) (a : Fin q → ℝ → ℝ),
    AbsolutelyContinuousOnInterval γ 0 1 ∧
    γ 0 = x ∧ γ 1 = y ∧
    (∀ i, AEMeasurable (a i) (volume.restrict (Icc (0 : ℝ) 1))) ∧
    IntegrableOn (fun t => Real.sqrt (∑ i, a i t ^ 2)) (Icc (0 : ℝ) 1) ∧
    (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      HasDerivAt γ (∑ i, a i t • X i (γ t)) t) ∧
    r = ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, Real.sqrt (∑ i, a i t ^ 2))}

/-- `u` is a local weak solution of the forward equation `∂ₜu = ∑ᵢⱼ Xᵢ(aᵢⱼ Xⱼ u)` on the
cylinder `I × U`, where `X₁, …, X_q` are the weight-one horizontal fields `G.horizontalFields hq`
of a Carnot group (for these divergence-free fields the weak identity below is the forward
equation). The function `u` is jointly measurable on `I × U`; there is a horizontal gradient `g`,
which for almost every time is the weak gradient `(X₁ u(t), …, X_q u(t))` on `U`; on every compact
`J × K ⊆ I × U`, `u ∈ L^∞(J; L²(K))` and `g ∈ L²(J × K)`; and for every smooth test function `φ`
compactly supported in `I × U`, `∫∫ (-u ∂ₜφ + ∑ᵢⱼ aᵢⱼ (Xⱼ u) (Xᵢ φ)) = 0`, with an integrable
integrand. -/
def IsLocalWeakSolution {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) : Prop :=
  let X := G.horizontalFields hq
  AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
    (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))) ∧
  ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
    (∀ᵐ t ∂(volume.restrict (I : Set ℝ)), ∀ i, hasWeakWordDeriv X U [i] (u t) (g i t)) ∧
    (∀ (J : Set ℝ) (K : Set (Fin N → ℝ)),
      IsCompact J → J ⊆ (I : Set ℝ) → IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
      essSup (fun t => eLpNorm (u t) 2 (volume.restrict K)) (volume.restrict J) < ⊤ ∧
      ∀ i, MemLp (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2) 2 (volume.restrict (J ×ˢ K))) ∧
    ∀ φ : ℝ × (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)) →
      Integrable (fun z : ℝ × (Fin N → ℝ) =>
        -(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
          ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) ∧
      ∫ z : ℝ × (Fin N → ℝ),
        (-(u z.1 z.2 * fderiv ℝ φ z (1, 0)) +
          ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 * fderiv ℝ φ z (0, X i z.2)) = 0

/-! ## The heat kernel -/

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Heat kernel with two-sided Gaussian bounds** for the sub-Laplacian `L = ∑ᵢ Xᵢ²` of a Carnot
group: there is a kernel `p`, smooth on `(0, ∞) × G × G`, solving the heat equation in `(t, x)`,
symmetric, satisfying the Chapman–Kolmogorov identity, of unit mass, with the delta initial
condition against bounded continuous functions, left-translation invariant, parabolically dilation
covariant, and obeying two-sided Gaussian bounds in the horizontal `ℓ²`-control distance
`d = horizontalL2Distance X`, with constants depending only on the group and its horizontal
fields. -/
theorem exists_heatKernel_gaussian
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq)) :
    let X := G.horizontalFields hq
    let L := sumSquares X
    let Q : ℝ := (G.homogeneousDimension : ℝ)
    let d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ :=
      fun x y => (horizontalL2Distance X x y).toReal
    ∃ p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × (Fin N → ℝ) × (Fin N → ℝ) => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ univ) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ,
        deriv (fun s => p s x y) t = L (fun w => p t w y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ, p t x y = p t y x) ∧
      (∀ s t : ℝ, 0 < s → 0 < t → ∀ x y : Fin N → ℝ,
        Integrable (fun z => p s x z * p t z y) ∧
        p (s + t) x y = ∫ z, p s x z * p t z y) ∧
      (∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, ∫ y, p t x y = 1) ∧
      (∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → (∃ M : ℝ, ∀ y, |φ y| ≤ M) →
        ∀ x : Fin N → ℝ,
          Tendsto (fun t => ∫ y, p t x y * φ y) (𝓝[>] 0) (𝓝 (φ x))) ∧
      (∀ t : ℝ, 0 < t → ∀ g x y : Fin N → ℝ, p t (G.mul g x) (G.mul g y) = p t x y) ∧
      (∀ t r : ℝ, 0 < t → 0 < r → ∀ x y : Fin N → ℝ,
        p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) = (r ^ G.homogeneousDimension)⁻¹ * p t x y) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ,
          c * t ^ (-Q / 2) * Real.exp (-(C * d x y ^ 2 / t)) ≤ p t x y ∧
          p t x y ≤ C * t ^ (-Q / 2) * Real.exp (-(c * d x y ^ 2 / t)) := by
  exact HeatKernel.exists_heatKernel_gaussian (Bridge.HomogeneousGroup.toLib G) hq hqpos hw
    hspan

/-! ## Poincaré, Harnack and Hölder estimates -/

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Horizontal Poincaré inequality** on a Carnot group: for every `1 ≤ p < ∞` there is `C` such
that for every open ball `B = B(x, r)` of the horizontal `ℓ²`-control distance and every `u` that
is `C¹` on a neighbourhood of the closure of `B`,
`(⨍_B |u - u_B|^p)^{1/p} ≤ C r (⨍_B |Xu|^p)^{1/p}`, where `|Xu|` is the Euclidean norm of the
horizontal gradient `(X₁ u, …, X_q u)`. -/
theorem horizontal_poincare
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (p : ℝ) (hp : 1 ≤ p) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (u : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ)),
        IsOpen U → closure (B x r) ⊆ U → ContDiffOn ℝ 1 u U →
        (⨍ y in B x r, |u y - ⨍ z in B x r, u z| ^ p) ^ (1 / p) ≤
          C * r * (⨍ y in B x r, Real.sqrt (∑ i, fieldDerivative (X i) u y ^ 2) ^ p) ^ (1 / p) := by
  exact HeatKernel.horizontal_poincare (Bridge.HomogeneousGroup.toLib G) hq hqpos hw hspan p hp

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Parabolic Harnack inequality** for measurable uniformly elliptic symmetric coefficients:
there is `H ≥ 1`, depending only on the group, its horizontal fields and `0 < lam ≤ Λ`, such that
every nonnegative local weak solution of `∂ₜu = ∑ᵢⱼ Xᵢ(aᵢⱼ Xⱼ u)` on `(s - 4r², s) × B(x, 2r)`
satisfies `ess sup_{(s - 3r², s - 2r²) × B(x, r)} u ≤ H · ess inf_{(s - r², s) × B(x, r)} u`. -/
theorem parabolic_harnack
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
        (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)) →
        (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
          (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧
          ∀ ξ : Fin q → ℝ,
            lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
            ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2) →
      ∀ (x : Fin N → ℝ) (r s : ℝ), 0 < r →
      ∀ u : ℝ → (Fin N → ℝ) → ℝ,
        IsLocalWeakSolution G hq hqpos hw hspan a ⟨Ioo (s - 4 * r ^ 2) s, isOpen_Ioo⟩
          ⟨interior (B x (2 * r)), isOpen_interior⟩ u →
        (∀ᵐ z ∂(volume.restrict (Ioo (s - 4 * r ^ 2) s ×ˢ B x (2 * r))), 0 ≤ u z.1 z.2) →
        essSup (fun z : ℝ × (Fin N → ℝ) => ENNReal.ofReal (u z.1 z.2))
            (volume.restrict (Ioo (s - 3 * r ^ 2) (s - 2 * r ^ 2) ×ˢ B x r)) ≤
          ENNReal.ofReal H *
            essInf (fun z : ℝ × (Fin N → ℝ) => ENNReal.ofReal (u z.1 z.2))
              (volume.restrict (Ioo (s - r ^ 2) s ×ˢ B x r)) := by
  exact HeatKernel.parabolic_harnack (Bridge.HomogeneousGroup.toLib G) hq hqpos hw hspan lam Λ
    hlam hlamΛ

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Hölder continuity of local weak solutions** for measurable uniformly elliptic symmetric
coefficients: there are `0 < α < 1` and `C > 0`, depending only on the group, its horizontal
fields and `0 < lam ≤ Λ`, such that every local weak solution `u` of `∂ₜu = ∑ᵢⱼ Xᵢ(aᵢⱼ Xⱼ u)` on
`Q = (t₀ - 4r², t₀) × B(x₀, 2r)` agrees almost everywhere on `Q' = (t₀ - r², t₀) × B(x₀, r)` with a
function `v` continuous on `Q'`, and whenever `m ≤ u ≤ M` almost everywhere on `Q`,
`|v(t, x) - v(s, y)| ≤ C ((d(x, y) + √|t - s|) / r)^α (M - m)` for `(t, x), (s, y) ∈ Q'`. -/
theorem parabolic_holder
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    let d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ :=
      fun x y => (horizontalL2Distance X x y).toReal
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
        (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)) →
        (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
          (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧
          ∀ ξ : Fin q → ℝ,
            lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
            ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2) →
      ∀ (x₀ : Fin N → ℝ) (r t₀ : ℝ), 0 < r →
      ∀ u : ℝ → (Fin N → ℝ) → ℝ,
        IsLocalWeakSolution G hq hqpos hw hspan a ⟨Ioo (t₀ - 4 * r ^ 2) t₀, isOpen_Ioo⟩
          ⟨interior (B x₀ (2 * r)), isOpen_interior⟩ u →
        ∃ v : ℝ → (Fin N → ℝ) → ℝ,
          (∀ᵐ z ∂(volume.restrict (Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r)), v z.1 z.2 = u z.1 z.2) ∧
          ContinuousOn (fun z : ℝ × (Fin N → ℝ) => v z.1 z.2) (Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r) ∧
          ∀ m M : ℝ,
            (∀ᵐ z ∂(volume.restrict (Ioo (t₀ - 4 * r ^ 2) t₀ ×ˢ B x₀ (2 * r))),
              m ≤ u z.1 z.2 ∧ u z.1 z.2 ≤ M) →
            ∀ z ∈ Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r, ∀ w ∈ Ioo (t₀ - r ^ 2) t₀ ×ˢ B x₀ r,
              |v z.1 z.2 - v w.1 w.2| ≤
                C * ((d z.2 w.2 + Real.sqrt |z.1 - w.1|) / r) ^ α * (M - m) := by
  exact HeatKernel.parabolic_holder (Bridge.HomogeneousGroup.toLib G) hq hqpos hw hspan lam Λ
    hlam hlamΛ

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Elliptic Harnack inequality** for measurable uniformly elliptic symmetric coefficients: there
is `H ≥ 1`, depending only on the group, its horizontal fields and `0 < lam ≤ Λ`, such that every
nonnegative `u ∈ W^{1,2}_{X,loc}(B(x, 2r))` with `∫ ∑ᵢⱼ aᵢⱼ (Xⱼ u) (Xᵢ φ) = 0` for all test
functions `φ` on `B(x, 2r)` satisfies `ess sup_{B(x, r)} u ≤ H · ess inf_{B(x, r)} u`. -/
theorem elliptic_harnack
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (lam Λ : ℝ) (hlam : 0 < lam) (hlamΛ : lam ≤ Λ) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ a : (Fin N → ℝ) → Fin q → Fin q → ℝ,
        (∀ i j, Measurable (fun x => a x i j)) →
        (∀ᵐ x ∂volume,
          (∀ i j, a x i j = a x j i) ∧
          ∀ ξ : Fin q → ℝ,
            lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j ∧
            ∑ i, ∑ j, a x i j * ξ i * ξ j ≤ Λ * ∑ i, ξ i ^ 2) →
      ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      let U : Opens (Fin N → ℝ) := ⟨interior (B x (2 * r)), isOpen_interior⟩
      ∀ u : (Fin N → ℝ) → ℝ,
        memSobolevXLoc noDriftWeight X U 1 2 u →
        (∃ g : Fin q → (Fin N → ℝ) → ℝ,
          (∀ i, hasWeakWordDeriv X U [i] u (g i)) ∧
          ∀ φ : TestFunction U ℝ (⊤ : ℕ∞),
            ∫ y in (U : Set (Fin N → ℝ)),
              ∑ i, ∑ j, a y i j * g j y * fieldDerivative (X i) φ y = 0) →
        (∀ᵐ y ∂(volume.restrict (B x (2 * r))), 0 ≤ u y) →
        essSup (fun y => ENNReal.ofReal (u y)) (volume.restrict (B x r)) ≤
          ENNReal.ofReal H * essInf (fun y => ENNReal.ofReal (u y)) (volume.restrict (B x r)) := by
  exact HeatKernel.elliptic_harnack (Bridge.HomogeneousGroup.toLib G) hq hqpos hw hspan lam Λ
    hlam hlamΛ

end HeatKernelChallenge

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib
public import Hormander.Interface
public import Hormander.Statements.MemSobolevOfIntegrable
public import Hormander.Statements.ExistsContDiffOfMemSobolev
public import Hormander.Statements.SubellipticEstimate
public import Hormander.Statements.LocalRegularity
import RothschildStein.Statements.exists_bch_lie_series
import RothschildStein.Statements.chow_rashevskii
import RothschildStein.Statements.exists_ball_box_compact_family
import RothschildStein.Statements.exists_ball_volume_doubling_compact_family
import RothschildStein.Statements.exists_distance_comparison_compact_family
public import RothschildStein.Statements.exists_lift_approximation_noDrift
import RothschildStein.Statements.exists_lift_approximation_drift

/-!
# Solution: Hörmander's theorem and the geometry of Hörmander vector fields, proved

This file repeats `Challenge.lean` verbatim and proves each of its theorems from the corresponding
theorem of the library (`Hormander.Interface.exists_smooth_aeRepresentative`, the theorems in
`Hormander.Statements` and in `RothschildStein.Statements`). The definitions below are
definitional copies of the library's; the bridges map the inductive type `LieWord` and the
structure `HomogeneousGroup` to and from the library's copies.

The Challenge statement follows.

## Hörmander's hypoellipticity theorem and the geometry of Hörmander vector fields

A standalone, Mathlib-only statement of Hörmander's theorem, its Sobolev-space companions, and
the algebraic and geometric theory of Hörmander vector fields used by Rothschild and Stein.
Space is `ℝⁿ = Fin n → ℝ` with Lebesgue measure (`EuclideanSpace ℝ (Fin N)` for the
Fourier-analytic companions); vector fields are maps `ℝⁿ → ℝⁿ`, acting by `Xf(x) = Df(x)·X(x)`.
Sources: L. Hörmander, *Hypoelliptic second order differential equations*, Acta Math. 119
(1967); M. Bramanti and L. Brandolini, *Hörmander Operators* (2023), cited as BB; A. Nagel,
E. M. Stein and S. Wainger, *Balls and metrics defined by vector fields I*, Acta Math. 155 (1985),
cited as NSW; L. P. Rothschild and E. M. Stein, Acta Math. 137 (1976).

* `hormander_hypoellipticity` (Hörmander 1967, Theorem 1.1). Let `X₀, …, X_k` be smooth vector
  fields on an open set `Ω` whose iterated Lie brackets span `ℝⁿ` at every point, and `c` smooth.
  If `u ∈ L¹_loc(Ω)` solves `X₀u + Σ Xᵢ²u + cu = g` weakly with `g` smooth, then `u` agrees a.e.
  on `Ω` with a smooth function.
* `memSobolev_neg_of_integrable`, `exists_contDiff_of_forall_memSobolev`, `subelliptic_estimate`,
  `forall_memSobolev_of_localized` (BB Propositions 5.17, 5.16(iii), Theorems 5.54, 5.64): the
  Sobolev-space steps of Hörmander's proof for `C_c^∞` coefficients on `ℝᴺ`: `L¹ ⊆ H^{-m}`,
  `⋂ₛ Hˢ ⊆ C^∞`, the subelliptic estimate, and localized regularity.
* `bch_lie_series` (BB Theorems 9.18 and 9.68): the formal Baker–Campbell–Hausdorff theorem. There
  are Lie polynomials `Cₙ` of degree `n` in two letters, `C₁ = x + y`, `C₂ = ½[x, y]`, with
  `exp x · exp y = exp (Σ_{n ≤ N} Cₙ)` modulo terms of degree `> N`, for every `N`; any other
  homogeneous series with this property coincides with `(Cₙ)` in the free associative algebra.
* `chow_rashevskii` (BB Theorem 1.45 and Proposition 1.28): on a connected open set,
  bracket-generating smooth fields connect any two points by finite chains of integral arcs (also
  locally); every control distance is finite; and `C¹` functions killed by all `Xᵢ` are constant.
* `ball_box`, `ball_volume_doubling`, `distance_comparison` (BB Theorems 9.11, 9.1 and 9.6; NSW
  Theorems 7, 1 and 2–4): the ball-box theorem, the volume formula `|B(x, r)| ≈ Λ(x, r)` with
  local doubling, and the comparison of the control distance with the distance defined by all
  brackets of bounded weight, uniformly on compact sets and over compact families of fields.
* `lifting_approximation`, `lifting_approximation_drift` (Rothschild–Stein lifting; BB Theorem
  10.6, corrected): Hörmander fields are lifted to free fields in more variables and approximated
  there by left-invariant fields of a free nilpotent homogeneous group.

The control distance `controlDistance Ω w X x y` is the infimum of `δ` such that a curve in `Ω`
joins `x` to `y` in unit time with velocity `Σ aᵢ Xᵢ`, `|aᵢ| ≤ δ^{wᵢ}`, where `wᵢ` is the weight of
`Xᵢ`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace Filter SchwartzMap FourierTransform
open scoped Topology ENNReal CompactConvergenceCLM

namespace HormanderChallenge

/-! ## Hörmander's theorem -/

/-- Formal Lie words in the letters `0, …, k`. -/
inductive LieWord (k : ℕ) where
  | generator : Fin (k + 1) → LieWord k
  | bracket : LieWord k → LieWord k → LieWord k

/-- The vector field obtained by evaluating a Lie word on the fields `X₀, …, X_k`. -/
def LieWord.eval {k N : ℕ} (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) :
    LieWord k → (Fin N → ℝ) → (Fin N → ℝ)
  | .generator i => X i
  | .bracket p q => VectorField.lieBracket ℝ (LieWord.eval X p) (LieWord.eval X q)

/-- Hörmander's condition: at every point of `Ω` the iterated brackets of `X` span `ℝᴺ`. -/
def LieAlgebraSpansOn {k N : ℕ} (Ω : Set (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ x ∈ Ω, Submodule.span ℝ (Set.range (fun w : LieWord k => LieWord.eval X w x)) = ⊤

/-- The Euclidean divergence `Σᵢ ∂ᵢVᵢ` of a vector field. -/
def euclideanDivergence {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (fderiv ℝ V x (Pi.single i 1)) i

/-- The formal adjoint `L*φ = -div(φX₀) + Σᵢ div(div(φXᵢ)Xᵢ) + cφ` of
`L = X₀ + Σ_{i=1}^k Xᵢ² + c`. -/
def hormanderAdjointTest {k N : ℕ} (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c : (Fin N → ℝ) → ℝ) (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  -euclideanDivergence (fun y => φ y • X 0 y) x +
    ∑ i : Fin k, euclideanDivergence
      (fun y => euclideanDivergence (fun q => φ q • X i.succ q) y • X i.succ y) x +
    c x * φ x

/-- `u ∈ L¹_loc(Ω)` is a weak solution of `X₀u + Σᵢ Xᵢ²u + cu = g` on `Ω`, with `g` smooth:
`∫_Ω u L*φ = ∫_Ω g φ` for every smooth `φ` with compact support in `Ω`. -/
def HasWeakHormanderEquation {k N : ℕ} (Ω : Set (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c g u : (Fin N → ℝ) → ℝ) : Prop :=
  LocallyIntegrableOn u Ω volume ∧ ContDiffOn ℝ (⊤ : ℕ∞) g Ω ∧
    ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, u x * hormanderAdjointTest X c φ x) = ∫ x in Ω, g x * φ x

namespace Bridge

/-- The library copy of a Lie word. -/
def LieWord.toLib {k : ℕ} : LieWord k → Hormander.Interface.LieWord k
  | .generator i => .generator i
  | .bracket p q => .bracket (LieWord.toLib p) (LieWord.toLib q)

theorem LieWord.eval_toLib {k N : ℕ} (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) :
    ∀ w : LieWord k, Hormander.Interface.LieWord.eval X (LieWord.toLib w) = LieWord.eval X w
  | .generator _ => rfl
  | .bracket p q => by
    simp only [LieWord.toLib, Hormander.Interface.LieWord.eval, LieWord.eval,
      LieWord.eval_toLib X p, LieWord.eval_toLib X q]

theorem lieAlgebraSpansOn {k N : ℕ} {Ω : Set (Fin N → ℝ)}
    {X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)} (h : LieAlgebraSpansOn Ω X) :
    Hormander.Interface.LieAlgebraSpansOn Ω X := by
  intro x hx
  refine top_le_iff.mp ((h x hx).symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨w, rfl⟩
  exact ⟨LieWord.toLib w, congrFun (LieWord.eval_toLib X w) x⟩

end Bridge

/-- **Hörmander's hypoellipticity theorem** (Hörmander 1967, Theorem 1.1). -/
theorem hormander_hypoellipticity {k N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c g u : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hspan : LieAlgebraSpansOn Ω X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω) (hEq : HasWeakHormanderEquation Ω X c g u) :
    ∃ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧ u =ᵐ[volume.restrict Ω] f := by
  exact Hormander.Interface.exists_smooth_aeRepresentative hΩ X c g u hX
    (Bridge.lieAlgebraSpansOn hspan) hc hEq

/-! ## Hörmander's estimates in Sobolev spaces `Hˢ = H^{s,2}(ℝᴺ)` -/

/-- Lie words evaluated on vector fields on a real normed space `E`. -/
def lieWordEval {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin (k + 1) → E → E) : LieWord k → E → E
  | .generator i => X i
  | .bracket p q => VectorField.lieBracket ℝ (lieWordEval X p) (lieWordEval X q)

/-- The length of a Lie word (its number of letters). -/
def lieWordLength {k : ℕ} : LieWord k → ℕ
  | .generator _ => 1
  | .bracket p q => lieWordLength p + lieWordLength q

/-- The vector field `V = Σᵢ Vⁱ ∂ᵢ` acting on complex tempered distributions on `ℝᴺ`. -/
def vectorFieldOp {N : ℕ} (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
    𝓢'(EuclideanSpace ℝ (Fin N), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin N), ℂ) :=
  ∑ i : Fin N,
    (TemperedDistribution.smulLeftCLM ℂ (fun x => ((V x i : ℝ) : ℂ))).comp
      (LineDeriv.lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)
        (EuclideanSpace.single i (1 : ℝ)))

/-- The operator `L = Σ_{i=1}^k Xᵢ² + X₀ + c` on complex tempered distributions on `ℝᴺ`
(meaningful for coefficients of temperate growth, such as the `C_c^∞` coefficients used here). -/
def hormanderOp {k N : ℕ} (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ) :
    𝓢'(EuclideanSpace ℝ (Fin N), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin N), ℂ) :=
  (∑ i : Fin k, (vectorFieldOp (X i.succ)).comp (vectorFieldOp (X i.succ))) +
    vectorFieldOp (X 0) + TemperedDistribution.smulLeftCLM ℂ (fun x => ((c x : ℝ) : ℂ))

namespace Bridge

theorem lieWordEval_toLib {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin (k + 1) → E → E) :
    ∀ w : LieWord k, Hormander.lieWordEval X (LieWord.toLib w) = lieWordEval X w
  | .generator _ => rfl
  | .bracket p q => by
    simp only [LieWord.toLib, Hormander.lieWordEval, lieWordEval,
      lieWordEval_toLib X p, lieWordEval_toLib X q]

theorem lieWordLength_toLib {k : ℕ} :
    ∀ w : LieWord k, Hormander.lieWordLength (LieWord.toLib w) = lieWordLength w
  | .generator _ => rfl
  | .bracket p q => by
    simp only [LieWord.toLib, Hormander.lieWordLength, lieWordLength,
      lieWordLength_toLib p, lieWordLength_toLib q]

end Bridge

/-- An integrable function lies in `H^{-m}` for every `m > N/2` (BB Proposition 5.17). -/
theorem memSobolev_neg_of_integrable {N : ℕ} {v : EuclideanSpace ℝ (Fin N) → ℂ}
    (hv : Integrable v) {m : ℝ} (hm : (N : ℝ) < 2 * m) :
    TemperedDistribution.MemSobolev (-m) 2 (Lp.toTemperedDistribution (hv.toL1 v)) := by
  exact Hormander.memSobolev_neg_of_integrable hv hm

/-- A tempered distribution in every `Hˢ` is a smooth function (BB Proposition 5.16(iii)). -/
theorem exists_contDiff_of_forall_memSobolev {N : ℕ} {T : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)}
    (hT : ∀ s : ℝ, TemperedDistribution.MemSobolev s 2 T) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin N), ℂ),
        Integrable (fun x => φ x * f x) ∧ T φ = ∫ x, φ x * f x := by
  exact Hormander.exists_contDiff_of_forall_memSobolev hT

/-- **Hörmander's subelliptic estimate** (BB Theorem 5.54) with gain `ε = 2/4^s`, for
`L = Σ_{i=1}^k Xᵢ² + X₀ + c` with real `C_c^∞` coefficients and Schwartz functions supported in a
compact `K`, when `N` Lie words of length `≤ s` form a basis on a neighbourhood `U` of `K`:
`∫ (1 + ‖ξ‖²)^ε |û(ξ)|² dξ ≤ C (‖Lu‖²_{L²} + ‖u‖²_{L²})`. -/
theorem subelliptic_estimate {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s) (w : Fin N → LieWord k) (hws : ∀ a, lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => lieWordEval X (w a) x)) :
    ∃ C : ℝ, ∀ u : 𝓢(EuclideanSpace ℝ (Fin N), ℂ), tsupport u ⊆ K →
      (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 4 ^ s) * ‖𝓕 (⇑u) ξ‖ ^ 2) ≤
        C * ((∫ x, ‖(∑ i : Fin k,
                fderiv ℝ (fun y => fderiv ℝ u y (X i.succ y)) x (X i.succ x)) +
              fderiv ℝ u x (X 0 x) + (c x : ℂ) * u x‖ ^ 2) +
            ∫ x, ‖u x‖ ^ 2) := by
  exact Hormander.subelliptic_estimate X c hX hXc hc hcc hK hU hKU s hs
    (fun a => Bridge.LieWord.toLib (w a))
    (fun a => (Bridge.lieWordLength_toLib (w a)).trans_le (hws a))
    (fun x hx => by simpa only [Bridge.lieWordEval_toLib] using hw x hx)

/-- **Local regularity** (BB Theorem 5.64): with `L`, `K`, `U` as in `subelliptic_estimate` and
cut-offs `ζ, ζ'`, `ζ' = 1` near `tsupport ζ`, `tsupport ζ' ⊆ K`: if `ζ' Lu` is a Schwartz
function and `ζ' u ∈ H^{-m}`, then `ζ u ∈ Hᵗ` for every `t`. -/
theorem forall_memSobolev_of_localized {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : Fin N → LieWord k)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => lieWordEval X (w a) x))
    {ζ ζ' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ')
    (hζζ' : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) (hζ'K : tsupport ζ' ⊆ K)
    (u : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) (f : 𝓢(EuclideanSpace ℝ (Fin N), ℂ))
    (hf : TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) (hormanderOp X c u) =
      (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)))
    {m : ℝ}
    (hm : TemperedDistribution.MemSobolev (-m) 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) u)) :
    ∀ t : ℝ, TemperedDistribution.MemSobolev t 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ)) u) := by
  exact Hormander.forall_memSobolev_of_localized X c hX hXc hc hcc hK hU hKU
    (fun a => Bridge.LieWord.toLib (w a))
    (fun x hx => by simpa only [Bridge.lieWordEval_toLib] using hw x hx) hζ hζ' hζζ' hζ'K u f hf hm

/-! ## The Baker–Campbell–Hausdorff formula -/

/-- The free Lie algebra on `x = of 0`, `y = of 1` embedded in the free associative algebra
`ℚ⟨x, y⟩`, through its universal enveloping algebra. -/
def lieToAssoc (a : FreeLieAlgebra ℚ (Fin 2)) : FreeAlgebra ℚ (Fin 2) :=
  FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℚ (Fin 2) (UniversalEnvelopingAlgebra.ι ℚ a)

/-- `exp a` computed in the truncation `ℚ⟨x, y⟩ / 𝔪^{N+1}`, `𝔪` the augmentation ideal. -/
def truncExp (N : ℕ) (a : FreeAlgebra ℚ (Fin 2)) :
    FreeAlgebra ℚ (Fin 2) ⧸
      RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] ℚ) ^ (N + 1) :=
  IsNilpotent.exp (Ideal.Quotient.mk
    (RingHom.ker (FreeAlgebra.algebraMapInv : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] ℚ) ^ (N + 1)) a)

/-- **Formal Baker–Campbell–Hausdorff theorem** (BB Theorems 9.18 and 9.68). `Cₙ` is a linear
combination of brackets `[z₁, [z₂, …, [z_{n-1}, zₙ]]]` of letters, of degree `n` in `ℚ⟨x, y⟩`. -/
theorem bch_lie_series :
    ∃ C : ℕ → FreeLieAlgebra ℚ (Fin 2),
      C 0 = 0 ∧
      C 1 = FreeLieAlgebra.of ℚ (0 : Fin 2) + FreeLieAlgebra.of ℚ (1 : Fin 2) ∧
      C 2 = (1 / 2 : ℚ) • ⁅FreeLieAlgebra.of ℚ (0 : Fin 2), FreeLieAlgebra.of ℚ (1 : Fin 2)⁆ ∧
      (∀ n : ℕ, C n ∈ Submodule.span ℚ
        {a : FreeLieAlgebra ℚ (Fin 2) | ∃ (l : List (Fin 2)) (j : Fin 2),
          l.length + 1 = n ∧
          a = l.foldr (fun i b => ⁅FreeLieAlgebra.of ℚ i, b⁆) (FreeLieAlgebra.of ℚ j)}) ∧
      (∀ n : ℕ, lieToAssoc (C n) ∈
        Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin 2 → FreeAlgebra ℚ (Fin 2))) ^ n) ∧
      (∀ N : ℕ, truncExp N (FreeAlgebra.ι ℚ 0) * truncExp N (FreeAlgebra.ι ℚ 1) =
        truncExp N (∑ n ∈ Finset.Icc 1 N, lieToAssoc (C n))) ∧
      ∀ S : ℕ → FreeAlgebra ℚ (Fin 2), S 0 = 0 →
        (∀ n : ℕ, S n ∈
          Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin 2 → FreeAlgebra ℚ (Fin 2))) ^ n) →
        (∀ N : ℕ, truncExp N (FreeAlgebra.ι ℚ 0) * truncExp N (FreeAlgebra.ι ℚ 1) =
          truncExp N (∑ n ∈ Finset.Icc 1 N, S n)) →
        ∀ n : ℕ, S n = lieToAssoc (C n) := by
  exact RothschildStein.exists_bch_lie_series

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

/-- Hörmander's condition at step `s`: brackets of words of weight `≤ s` span `ℝⁿ` on `Ω`. -/
def bracketStepOn {m n : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (s : ℕ) : Prop :=
  ∀ x ∈ Ω, Submodule.span ℝ
    {v | ∃ I : List (Fin m), I ≠ [] ∧ wordWeight w I ≤ s ∧ v = wordBracket X I x} = ⊤

/-! ## Control distance -/

/-- `γ : [0, 1] → Ω` is absolutely continuous with `γ' = Σᵢ aᵢ Xᵢ(γ)` a.e., `|aᵢ| ≤ δ^{wᵢ}`. -/
def isControlledCurve {m n : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (δ : ℝ) (γ : ℝ → (Fin n → ℝ)) : Prop :=
  0 < δ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧ MapsTo γ (Icc 0 1) Ω ∧
  ∃ a : Fin m → ℝ → ℝ,
    (∀ i, AEMeasurable (a i) (volume.restrict (Icc (0 : ℝ) 1))) ∧
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      (∀ i, |a i t| ≤ δ ^ (w i : ℕ)) ∧ HasDerivAt γ (∑ i, a i t • X i (γ t)) t

/-- The weighted control (Carnot–Carathéodory) distance in `Ω` (`∞` if no curve exists). -/
def controlDistance {m n : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y : Fin n → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ δ : ℝ, r = ENNReal.ofReal δ ∧
    ∃ γ : ℝ → (Fin n → ℝ), isControlledCurve Ω w X δ γ ∧ γ 0 = x ∧ γ 1 = y}

/-- The control ball `{y ∈ Ω | d(x, y) < r}`. -/
def rsBall {a n : ℕ} (Ω : Set (Fin n → ℝ)) (p : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  {y ∈ Ω | controlDistance Ω p X x y < ENNReal.ofReal r}

/-! ## Subelliptic geometry -/

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Chow–Rashevskii theorem** (BB Theorem 1.45 and Proposition 1.28). `arc D a b`: `a` and `b`
are joined in `D` by a `C¹` integral curve of a constant multiple `cXᵢ` of one field. -/
theorem chow_rashevskii {m n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hrank : bracketSpansOn Ω X) :
    let arc : Set (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → Prop :=
      fun D a b => ∃ (i : Fin m) (c : ℝ) (γ : ℝ → Fin n → ℝ),
        ContDiffOn ℝ 1 γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) D ∧
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (c • X i (γ t)) t) ∧ γ 0 = a ∧ γ 1 = b
    (∀ x ∈ Ω, ∀ W : Set (Fin n → ℝ), IsOpen W → x ∈ W → W ⊆ Ω →
      ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
        ∀ a ∈ U, ∀ b ∈ U, Relation.EqvGen (arc W) a b) ∧
    (∀ x ∈ Ω, ∀ y ∈ Ω, Relation.EqvGen (arc Ω) x y) ∧
    (∀ w : Fin m → ℕ+, ∀ x ∈ Ω, ∀ y ∈ Ω, controlDistance Ω w X x y ≠ ∞) ∧
    (∀ f : (Fin n → ℝ) → ℝ, ContDiffOn ℝ 1 f Ω →
      (∀ z ∈ Ω, ∀ i, fderiv ℝ f z (X i z) = 0) → ∀ x ∈ Ω, ∀ y ∈ Ω, f y = f x) := by
  exact RothschildStein.chow_rashevskii hΩ hconn X hX hrank

/-- The absolute Jacobian determinant `|det DF(x)|`. -/
def absoluteJacobian {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) : ℝ :=
  |(LinearMap.toMatrix (Pi.basisFun ℝ (Fin N)) (Pi.basisFun ℝ (Fin N))
    (fderiv ℝ f x).toLinearMap).det|

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Nagel–Stein–Wainger ball-box theorem** (BB Theorem 9.11; NSW Theorem 7), uniformly for
`x ∈ K` and over a compact family `X σ` of weighted fields that is jointly smooth and satisfies
Hörmander's condition at step `s` on `V ⊇ K`. For every `θ`-maximal choice `B` of `n` words
(`|det(X_{B j}(x))| r^{Σ weight(B j)}` within the factor `θ` of its maximum), the map
`F(u) = exp(Σⱼ uⱼ X_{B j})(x)` is smooth and injective on the box `Q`, with Jacobian comparable to
`λ = det(X_{B j}(x))`, and `F(Q)` lies between the control balls of radii `br` and `Cr`. -/
theorem ball_box {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg]
    {k n s : ℕ} (hn : 0 < n) (w : Fin (k + 1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hVΩ : V ⊆ Ω)
    (X : Sg → Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hjoint : ∀ i j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ Ω))
    (hstep : ∀ σ, bracketStepOn V w (X σ) s)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ a b C r₀ : ℝ, 0 < a ∧ 0 < b ∧ 0 < C ∧ 0 < r₀ ∧
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B : Fin n → List (Fin (k + 1)), (∀ j, wordWeight w (B j) ≤ s) →
      (∀ B' : Fin n → List (Fin (k + 1)), (∀ j, wordWeight w (B' j) ≤ s) →
        θ * (|(Matrix.of fun i j => wordBracket (X σ) (B' j) x i).det| *
              r ^ (∑ j, wordWeight w (B' j))) ≤
          |(Matrix.of fun i j => wordBracket (X σ) (B j) x i).det| *
            r ^ (∑ j, wordWeight w (B j))) →
      let Q : Set (Fin n → ℝ) := {u | ∀ j, |u j| < (a * r) ^ wordWeight w (B j)}
      let lam : ℝ := (Matrix.of fun i j => wordBracket (X σ) (B j) x i).det
      ∃ F : (Fin n → ℝ) → (Fin n → ℝ),
        (∀ u ∈ Q, ∃ γ : ℝ → (Fin n → ℝ), γ 0 = x ∧ γ 1 = F u ∧
          ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Ω ∧
            HasDerivWithinAt γ (∑ j, u j • wordBracket (X σ) (B j) (γ t)) (Icc 0 1) t) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) F Q ∧ InjOn F Q ∧
        (∀ u ∈ Q, |lam| / 4 ≤ absoluteJacobian F u ∧ absoluteJacobian F u ≤ 4 * |lam|) ∧
        rsBall Ω w (X σ) x (b * r) ⊆ F '' Q ∧ F '' Q ⊆ rsBall Ω w (X σ) x (C * r) := by
  exact RothschildStein.exists_ball_box_compact_family hn w hw hΩ hV hK hKV hVΩ X hX hjoint
    hstep θ hθ hθ1

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Volume of control balls and local doubling** (BB Theorem 9.1 and p. 400; NSW Theorem 1),
uniformly as in `ball_box`: `|B(x, r)| ≈ Λ(x, r) = Σ_B |det(X_{B j}(x))| r^{Σ weight(B j)}`, the
sum over all `n`-tuples of words of weight `≤ s`. -/
theorem ball_volume_doubling {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg]
    {k n s : ℕ} (hn : 0 < n) (w : Fin (k + 1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hVΩ : V ⊆ Ω)
    (X : Sg → Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hjoint : ∀ i j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ Ω))
    (hstep : ∀ σ, bracketStepOn V w (X σ) s) :
    ∃ c C L r₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < L ∧ 0 < r₀ ∧
      ∀ σ, ∀ x ∈ K,
      (∀ r : ℝ, 0 < r → r ≤ r₀ →
        let Λ : ℝ := ∑ B ∈ Fintype.piFinset (fun _ : Fin n => wordFamily w s),
          |(Matrix.of fun i j => wordBracket (X σ) (B j) x i).det| *
            r ^ (∑ j, wordWeight w (B j))
        0 < Λ ∧
        ENNReal.ofReal (c * Λ) ≤ volume (rsBall Ω w (X σ) x r) ∧
        volume (rsBall Ω w (X σ) x r) ≤ ENNReal.ofReal (C * Λ)) ∧
      (∀ A r : ℝ, 1 ≤ A → 0 < r → A * r ≤ r₀ →
        volume (rsBall Ω w (X σ) x (A * r)) ≤
          ENNReal.ofReal (L * A ^ (n * s)) * volume (rsBall Ω w (X σ) x r)) := by
  exact RothschildStein.exists_ball_volume_doubling_compact_family hn w hw hΩ hV hK hKV hVΩ X
    hX hjoint hstep

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Comparison of control distances** (BB Theorem 9.6 and Remark 9.5; NSW Theorems 2–4),
uniformly as in `ball_box`: near `K`, the control distance `d` of `X` is comparable to the
control distance `d*` of the family of all brackets `X_I`, `weight(I) ≤ s`, each with weight
`weight(I)` (enumerated by `e`). -/
theorem distance_comparison {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg]
    {k n s : ℕ} (hn : 0 < n) (w : Fin (k + 1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hVΩ : V ⊆ Ω)
    (X : Sg → Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hjoint : ∀ i j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ Ω))
    (hstep : ∀ σ, bracketStepOn V w (X σ) s) :
    let e : Fin (wordFamily w s).card → List (Fin (k + 1)) :=
      fun j => ((wordFamily w s).equivFin.symm j).val
    let ws : Fin (wordFamily w s).card → ℕ+ := fun j => Nat.toPNat' (wordWeight w (e j))
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ σ, ∀ x ∈ K, ∀ y : Fin n → ℝ,
        controlDistance Ω ws (fun j => wordBracket (X σ) (e j)) x y < ENNReal.ofReal ε →
        controlDistance Ω ws (fun j => wordBracket (X σ) (e j)) x y ≤
            controlDistance Ω w (X σ) x y ∧
          controlDistance Ω w (X σ) x y ≤
            ENNReal.ofReal C * controlDistance Ω ws (fun j => wordBracket (X σ) (e j)) x y := by
  exact RothschildStein.exists_distance_comparison_compact_family hn w hw hΩ hV hK hKV hVΩ X
    hX hjoint hstep


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

end HomogeneousGroup

/-! ## Free nilpotent algebras and the lifting theorem -/

/-- The bounded words: words of weight `≤ s` for the weights `p`. -/
abbrev BoundedWord (a s : ℕ) (p : Fin a → ℕ+) := ↥(wordFamily p s)

/-- The underlying list of a bounded word. -/
def boundedWordList {a s : ℕ} {p : Fin a → ℕ+} (I : BoundedWord a s p) : List (Fin a) := I.val

/-- Coefficient vectors indexed by bounded words: the free associative algebra truncated at
weight `s`. -/
abbrev WordCoefficients (a s : ℕ) (p : Fin a → ℕ+) := BoundedWord a s p → ℝ

/-- The concatenation product `(f g)(J) = Σ_{J = J₁J₂} f(J₁) g(J₂)` of word coefficients. -/
def wordConvolution {a : ℕ} (f g : List (Fin a) → ℝ) (J : List (Fin a)) : ℝ :=
  ∑ r ∈ Finset.range (J.length + 1), f (J.take r) * g (J.drop r)

/-- The formal bracket `[e_{i₁}, [e_{i₂}, …, e_{iⱼ}]]` in the free associative algebra. -/
def formalBracket {a : ℕ} : List (Fin a) → List (Fin a) → ℝ
  | [] => fun _ => 0
  | [i] => fun J => if J = [i] then 1 else 0
  | i :: j :: I => fun J =>
      wordConvolution (fun K => if K = [i] then 1 else 0) (formalBracket (j :: I)) J -
      wordConvolution (formalBracket (j :: I)) (fun K => if K = [i] then 1 else 0) J

/-- The formal bracket truncated to bounded words. -/
def truncatedBracket {a s : ℕ} {p : Fin a → ℕ+} (I : List (Fin a)) : WordCoefficients a s p :=
  fun J => formalBracket I (boundedWordList J)

/-- The free nilpotent Lie algebra of step `s`: the span of the truncated brackets of nonempty
words of weight `≤ s`. -/
def formalSpan (a s : ℕ) (p : Fin a → ℕ+) : Submodule ℝ (WordCoefficients a s p) :=
  Submodule.span ℝ {f | ∃ I : List (Fin a), I ≠ [] ∧ wordWeight p I ≤ s ∧ f = truncatedBracket I}

/-- The dimension of the free nilpotent Lie algebra of step `s`. -/
def freeDimension (a s : ℕ) (p : Fin a → ℕ+) : ℕ := Module.finrank ℝ (formalSpan a s p)

/-- `Σ_I c_I [e_I] = 0` in the free nilpotent Lie algebra. -/
def FormalRelation {a s : ℕ} {p : Fin a → ℕ+} (c : BoundedWord a s p → ℝ) : Prop :=
  (∑ I, c I • (truncatedBracket (boundedWordList I) : WordCoefficients a s p)) = 0

/-- `X` is free up to step `s` at `x`: the only linear relations among the brackets `X_I(x)`,
`weight(I) ≤ s`, are those holding in the free nilpotent Lie algebra. -/
def FreeAt {a n : ℕ} (p : Fin a → ℕ+) (s : ℕ)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∀ c : BoundedWord a s p → ℝ,
    (∑ I, c I • wordBracket X (boundedWordList I) x) = 0 ↔ FormalRelation c

/-- Hörmander's condition at step `s` at the point `x`. -/
def StepSpansAt {a n : ℕ} (p : Fin a → ℕ+) (s : ℕ)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  Submodule.span ℝ {v | ∃ I : List (Fin a), I ≠ [] ∧ wordWeight p I ≤ s ∧
    v = wordBracket X I x} = ⊤

/-- The iterated partial derivative `∂_{j₁} ⋯ ∂_{jₗ} f`. -/
def rsPartial {N : ℕ} : List (Fin N) → ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ
  | [] => fun f => f
  | j :: J => fun f u => fderiv ℝ (rsPartial J f) u (Pi.single j 1)

/-- `R` has local weight `≥ a` at `0`: every derivative `∂_J R_j(0)` with
`Σ ω(J) < a + ω_j` vanishes. -/
def WeightedJet {N : ℕ} (ω : Fin N → ℕ) (a : ℤ) (R : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ j J, (((J.map ω).sum) : ℤ) < a + (ω j : ℤ) → rsPartial J (fun u => R u j) 0 = 0

/-- The projection `ℝ^{n+m} → ℝⁿ` onto the first `n` coordinates. -/
def basePoint {n m : ℕ} (ξ : Fin (n + m) → ℝ) : Fin n → ℝ := fun j => ξ (Fin.castAdd m j)

/-- The point `(x, t) ∈ ℝ^{n+m}`. -/
def joinPoint {n m : ℕ} (x : Fin n → ℝ) (t : Fin m → ℝ) : Fin (n + m) → ℝ := Fin.addCases x t

/-- The lifted fields `X̃ᵢ(x, t) = (Xᵢ(x), (P_{il}(x, t))_l)` on `ℝ^{n+m}`. -/
def triangularLift {a n m : ℕ} (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ) :
    Fin a → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) :=
  fun i ξ => Fin.addCases (X i (basePoint ξ)) (fun l => MvPolynomial.eval ξ (P i l))

/-- The homogeneous gauge `max_j |u_j|^{1/ω_j}`. -/
def rsGauge {N : ℕ} (ω : Fin N → ℕ) (_hω : ∀ j, 0 < ω j) (u : Fin N → ℝ) : ℝ :=
  sSup (Set.range (fun j => Real.rpow |u j| ((ω j : ℝ)⁻¹)))

/-- The measure of the fiber `{t | (z, t) ∈ A}`. -/
def fiberVolume {n m : ℕ} (A : Set (Fin (n + m) → ℝ)) (z : Fin n → ℝ) : ℝ≥0∞ :=
  volume {t : Fin m → ℝ | joinPoint z t ∈ A}

/-- The conclusion of the lifting and approximation theorem for fields `X` on `Ω` with weights
`w`, at `x₀`, with step `s` and dilation exponents `κ` (BB Theorem 10.6, corrected): polynomial
fields `P` lift `X` to fields `X̃ = triangularLift X P` on `ℝ^{n+m}`, `n + m` the dimension of the
free nilpotent Lie algebra, that are free and bracket-generating up to step `s` on a neighbourhood
`U` of `(x₀, 0)`. `G` is a homogeneous group (with inverse `-u`) whose left-invariant fields `Y`,
homogeneous of degree `κ`, are free of step `s` with brackets `Y_{B j}` spanning at every point,
`B` a basis of bracket words. `Θ(η, ξ)` (exponential coordinates `e η`, antisymmetric) satisfies
`DΘ(η)·X̃_I = Y_I ∘ Θ + R_I ∘ Θ`, the remainders `R_I` having local weight `≥ 1 - weight(I)` and
vanishing at `0` for `weight(I) ≤ s`; the Jacobians of `Θ` in each variable are controlled by
`c`, `ωp`, `ωm`; the gauge `|Θ(η, ξ)|` is comparable to the control distance of `X̃`; integration
over the fibers maps test functions on `U` to test functions on `Ω`; and lifted balls have volume
`≈ r^Q`, project into the balls of `X`, and have fiber volumes `≈ |B̃|/|B|`. -/
def LiftingApproximation {n a : ℕ} (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (s : ℕ) (w : Fin a → ℕ+)
    (κ : Fin a → ℤ) : Prop :=
  ∃ m : ℕ, n + m = freeDimension a s w ∧
  ∃ P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ,
  ∃ U : Set (Fin (n + m) → ℝ),
  ∃ G : HomogeneousGroup (n + m),
  ∃ B : Fin (n + m) → List (Fin a),
  ∃ v : Fin a → (Fin (n + m) → ℝ),
  ∃ Y : Fin a → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
  ∃ Θ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
  ∃ e : (Fin (n + m) → ℝ) → OpenPartialHomeomorph
    (Fin (n + m) → ℝ) (Fin (n + m) → ℝ),
  ∃ R : List (Fin a) → (Fin (n + m) → ℝ) →
    (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
  ∃ c : (Fin (n + m) → ℝ) → ℝ,
  ∃ ωp ωm : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ,
  let Xl := triangularLift X P
  let O := {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω}
  let T := {z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) |
    z.1 ∈ U ∧ z.2 ∈ (e z.1).target}
  (∀ i l, ∀ j ∈ (P i l).vars, j.val < n + l.val) ∧
  IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ O ∧
  joinPoint x₀ (0 : Fin m → ℝ) ∈ U ∧
  (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xl i) O) ∧
  (∀ ξ ∈ U, FreeAt w s Xl ξ ∧ StepSpansAt w s Xl ξ) ∧
  (∀ j, B j ≠ [] ∧ wordWeight w (B j) ≤ s ∧ G.weight j = wordWeight w (B j)) ∧
  LinearIndependent ℝ (fun j => (truncatedBracket (B j) : WordCoefficients a s w)) ∧
  Submodule.span ℝ (Set.range (fun j =>
    (truncatedBracket (B j) : WordCoefficients a s w))) = formalSpan a s w ∧
  (∀ i, (∑ j, v i j • (truncatedBracket (B j) : WordCoefficients a s w)) =
    truncatedBracket [i]) ∧
  (∀ u, (fun j => MvPolynomial.eval u (G.inversePolynomial j)) = -u) ∧
  (∀ i u, Y i u = fderiv ℝ (G.mul u) 0 (v i)) ∧
  (∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i)) ∧
  (∀ i u z, fderiv ℝ (G.mul u) z (Y i z) = Y i (G.mul u z)) ∧
  (∀ i t, 0 < t → ∀ u,
    Y i (G.dilate t u) = t ^ κ i • G.dilate t (Y i u)) ∧
  (∀ u, FreeAt w s Y u ∧ StepSpansAt w s Y u) ∧
  (∀ I : List (Fin a), s < wordWeight w I → wordBracket Y I = 0) ∧
  (∀ j, wordBracket Y (B j) 0 = Pi.single j 1) ∧
  (∀ u, (∑ j, u j • wordBracket Y (B j) u) = u) ∧
  ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Θ z.1 z.2) (U ×ˢ U) ∧
  (∀ η ∈ U, (e η).source = U ∧
    (∀ ξ ∈ U, e η ξ = Θ η ξ) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (e η) (e η).source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (e η).symm (e η).target ∧ Θ η η = 0) ∧
  (∀ η ∈ U, ∀ u ∈ (e η).target,
    ∃ γ : ℝ → (Fin (n + m) → ℝ), γ 0 = η ∧ γ 1 = (e η).symm u ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ O ∧
        HasDerivAt γ (∑ j, u j • wordBracket Xl (B j) (γ t)) t)) ∧
  (∀ η ∈ U, ∀ ξ ∈ U, Θ ξ η = -Θ η ξ) ∧
  IsOpen T ∧
  (∀ I, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => R I z.1 z.2) T) ∧
  (∀ I, I ≠ [] → ∀ η ∈ U,
    WeightedJet G.weight (1 - (wordWeight w I : ℤ)) (R I η)) ∧
  (∀ I, I ≠ [] → wordWeight w I ≤ s → ∀ η ∈ U, R I η 0 = 0) ∧
  (∀ I, I ≠ [] → ∀ η ∈ U, ∀ ξ ∈ U,
    fderiv ℝ (Θ η) ξ (wordBracket Xl I ξ) =
      wordBracket Y I (Θ η ξ) + R I η (Θ η ξ)) ∧
  ContDiffOn ℝ (⊤ : ℕ∞) c U ∧ (∀ η ∈ U, 0 < c η) ∧
  ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωp z.1 z.2) T ∧
  ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ωm z.1 z.2) T ∧
  (∀ η ∈ U, ωp η 0 = 0 ∧ ωm η 0 = 0) ∧
  (∀ η ∈ U, ∀ u, ωm η u = ωp η (-u)) ∧
  (∀ η ∈ U, ∀ ξ ∈ U,
    0 < 1 + ωp η (Θ η ξ) ∧ 0 < 1 + ωm ξ (Θ η ξ) ∧
    absoluteJacobian (Θ η) ξ = (c η * (1 + ωp η (Θ η ξ)))⁻¹ ∧
    absoluteJacobian (fun ζ => Θ ζ ξ) η = (c ξ * (1 + ωm ξ (Θ η ξ)))⁻¹) ∧
  (∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
    ∃ cmin cmax C r : ℝ, 0 < cmin ∧ 0 < cmax ∧ 0 < C ∧ 0 < r ∧
      (∀ η ∈ K, cmin ≤ c η ∧ c η ≤ cmax) ∧
      (∀ η ∈ K, ∀ u ∈ (e η).target, ‖u‖ < r →
        |ωp η u| ≤ C * ‖u‖ ∧ |ωm η u| ≤ C * ‖u‖)) ∧
  (∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ η ∈ U, ∀ ξ ∈ U,
    ENNReal.ofReal (rsGauge G.weight G.weight_pos (Θ η ξ) / Cρ) ≤ controlDistance O w Xl η ξ ∧
    controlDistance O w Xl η ξ ≤ ENNReal.ofReal (Cρ * rsGauge G.weight G.weight_pos (Θ η ξ))) ∧
  (∀ V : Opens (Fin (n + m) → ℝ), (V : Set _) = U →
    ∃ F : TestFunction V ℝ (⊤ : ℕ∞) →L_c[ℝ]
      TestFunction (⟨Ω, hΩ⟩ : Opens (Fin n → ℝ)) ℝ (⊤ : ℕ∞),
      ∀ φ x, F φ x = ∫ t : Fin m → ℝ, φ (joinPoint x t)) ∧
  (∀ K : Set (Fin (n + m) → ℝ), IsCompact K → K ⊆ U →
    ∃ rstar cv Cv δ cf Cf : ℝ,
      0 < rstar ∧ 0 < cv ∧ 0 < Cv ∧ 0 < δ ∧ δ < 1 ∧ 0 < cf ∧ 0 < Cf ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
        let Ul := rsBall O w Xl η r
        let Vb := rsBall Ω w X (basePoint η) r
        Ul ⊆ U ∧ MeasurableSet Ul ∧ MeasurableSet Vb ∧
        volume Ul ≠ ⊤ ∧ volume Vb ≠ ⊤ ∧
        0 < (volume Ul).toReal ∧ 0 < (volume Vb).toReal ∧
        cv * r ^ G.homogeneousDimension ≤ (volume Ul).toReal ∧
        (volume Ul).toReal ≤ Cv * r ^ G.homogeneousDimension ∧
        (∀ ξ ∈ Ul, controlDistance Ω w X (basePoint η) (basePoint ξ) ≤
          controlDistance O w Xl η ξ) ∧
        (∀ z : Fin n → ℝ,
          fiberVolume Ul z ≤ ENNReal.ofReal (Cf * (volume Ul).toReal / (volume Vb).toReal)) ∧
        (∀ z ∈ rsBall Ω w X (basePoint η) (δ * r),
          ENNReal.ofReal (cf * (volume Ul).toReal / (volume Vb).toReal) ≤ fiberVolume Ul z))

namespace Bridge

/-- A homogeneous group of the library, as a Challenge homogeneous group. -/
def HomogeneousGroup.ofLib {N : ℕ} (G : RothschildStein.HomogeneousGroup N) :
    HomogeneousGroup N :=
  ⟨G.dimension_pos, G.weight, G.weight_pos, G.weight_mono, G.productPolynomial,
    G.inversePolynomial, G.zero_left, G.zero_right, G.assoc, G.inverse_left, G.inverse_right,
    G.dilation_product⟩

end Bridge

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Lifting and approximation without drift** (Rothschild–Stein; BB Theorem 10.6, corrected):
smooth fields `X₁, …, X_q` satisfying Hörmander's condition of step `s ≥ 2` at `x₀` can be lifted
and approximated by a free nilpotent homogeneous group. -/
theorem lifting_approximation {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ Ω)
    (s : ℕ) (hs : 2 ≤ s) (hspan : StepSpansAt (fun _ : Fin q => 1) s X x₀) :
    LiftingApproximation Ω hΩ X x₀ s (fun _ => 1) (fun _ => -1) := by
  unfold LiftingApproximation
  obtain ⟨m, hm, P, U, G, h⟩ :=
    RothschildStein.exists_lift_approximation_noDrift hn hq Ω hΩ X hX x₀ hx₀ s hs hspan
  exact ⟨m, hm, P, U, Bridge.HomogeneousGroup.ofLib G, h⟩

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Lifting and approximation with drift** (BB Theorem 10.6, corrected): the same for
`X₀, X₁, …, X_q`, the drift `X₀` having weight two. -/
theorem lifting_approximation_drift {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ Ω)
    (s : ℕ) (hs : 2 ≤ s)
    (hspan : StepSpansAt (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s X x₀) :
    LiftingApproximation Ω hΩ X x₀ s (fun i => if i = 0 then 2 else 1)
      (fun i => if i = 0 then -2 else -1) := by
  unfold LiftingApproximation
  obtain ⟨m, hm, P, U, G, h⟩ :=
    RothschildStein.exists_lift_approximation_drift hn hq Ω hΩ X hX x₀ hx₀ s hs hspan
  exact ⟨m, hm, P, U, Bridge.HomogeneousGroup.ofLib G, h⟩

end HormanderChallenge

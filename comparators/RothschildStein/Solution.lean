-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib
import RothschildStein.Statements.rs3_no_drift_sobolev
import RothschildStein.Statements.rs3_no_drift_holder
import RothschildStein.Statements.rs3_drift_sobolev
import RothschildStein.Statements.rs3_drift_holder
public import RothschildStein.Statements.rs2a_noDrift
import RothschildStein.Statements.rs2a_drift
import RothschildStein.Statements.rs2b_noDrift
import RothschildStein.Statements.rs2b_drift

/-!
# Solution: the Rothschild–Stein estimates, proved

This file repeats `Challenge.lean` verbatim and proves each of its theorems from the corresponding
theorem in `RothschildStein.Statements`. The definitions below are definitional copies of the
library's; the bridges map the structures `HomogeneousGroup` and `SmoothDifferentialOperator` to
the library's copies.

The Challenge statement follows.

## The Rothschild–Stein estimates for Hörmander operators

A standalone, Mathlib-only statement of the Rothschild–Stein regularity theory for `L = Σ Xᵢ²`
and `L = X₀ + Σ Xᵢ²`, after M. Bramanti and L. Brandolini, *Hörmander Operators* (2023), cited as
BB. Space is `ℝⁿ = Fin n → ℝ` with Lebesgue measure; fields act by `Xf(x) = Df(x)·X(x)`.

* `rothschildStein_sobolev`, `rothschildStein_holder` (BB Theorem 11.1). For `L = Σ Xᵢ²` with
  bracket-generating smooth fields on `Ω`, a distribution `T` with `LT = f ∈ W^{k,p}_X(Ω)` (resp.
  `C^{k,α}_X(Ω)`) is a function `u ∈ W^{k+2,p}_{X,loc}(Ω)` (resp. `C^{k+2,α}_{X,loc}(Ω)`) with
  `‖u‖_{k+2,V} ≤ C (‖f‖_{k,W} + ‖u‖_{L^p(W)})` (resp. `L^∞(W)`) for `V ⋐ W ⋐ Ω`, `1 < p < ∞`,
  `0 < α < 1`; in the Hölder case `Lu = f` holds pointwise with intrinsic derivatives.
* `rothschildStein_sobolev_drift`, `rothschildStein_holder_drift` (BB Theorem 11.2): the same for
  `L = X₀ + Σ Xᵢ²` at `k = 0`, the drift `X₀` having weight two.
* `fundamental_solution`, `fundamental_solution_drift` (BB Theorem 11.5): on a homogeneous group
  with `Q ≥ 3`, `Σ Zᵢ²` (resp. `Z₀ + Σ Zᵢ²`) has a unique fundamental solution homogeneous of
  degree `2 - Q`, with the kernel bounds and representation formulas of the parametrix.
* `global_estimates`, `global_estimates_drift` (BB §8.4–§8.6): global, local and scale-invariant
  `Lᵖ` and Hölder estimates on homogeneous groups; local regularity; bounded-domain solvability.

The supporting theorems `HomogeneousGroup.horizontalFields_contDiff`, `.driftFields_contDiff`
and `testMultiplierOn_spec` (smoothness facts) supply proof arguments inside the statements;
they are compared by statement.

`controlDistance Ω w X x y` is the infimum of `δ` such that a curve in `Ω` joins `x` to `y` in unit
time with velocity `Σ aᵢXᵢ`, `|aᵢ| ≤ δ^{wᵢ}`. `X`-Sobolev and `X`-Hölder norms of order `k` use the
words of weight `≤ k`, through weak derivatives or derivatives along integral curves.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped Topology ENNReal

namespace RothschildSteinChallenge

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

/-- Weights with drift: `X₀` has weight two, `X₁, …, X_q` weight one. -/
def driftWeight {q : ℕ} (i : Fin (q + 1)) : ℕ+ := if i = 0 then 2 else 1

/-- Weights without drift: every field has weight one. -/
def noDriftWeight {q : ℕ} (_i : Fin q) : ℕ+ := 1

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


/-! ## The equations `ΣXᵢ²u = f` and `X₀u + ΣXᵢ²u = f` in the sense of distributions -/

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

/-- `φ · a` is a test function on `Ω` for `a` smooth on `Ω` (supporting lemma). -/
theorem testMultiplierOn_spec {n : ℕ} (Ω : Opens (Fin n → ℝ)) (a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ))) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * a x) ∧ HasCompactSupport (fun x => φ x * a x) ∧
      tsupport (fun x => φ x * a x) ⊆ (Ω : Set (Fin n → ℝ)) := by
  refine ⟨?_, φ.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans φ.tsupport_subset⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
  · exact φ.contDiff.contDiffAt.mul (ha.contDiffAt (Ω.isOpen.mem_nhds hx))
  · have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport (φ : (Fin n → ℝ) → ℝ) :=
      isClosed_closure.isOpen_compl.mem_nhds fun h => hx (φ.tsupport_subset h)
    exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Fin n → ℝ => (0 : ℝ)) x)
      |>.congr_of_eventuallyEq (he.mono fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])

/-- Multiplication of a test function on `Ω` by a function smooth on `Ω`. -/
def testMultiplierOn {n : ℕ} (Ω : Opens (Fin n → ℝ)) (a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
  ⟨fun x => φ x * a x, (testMultiplierOn_spec Ω a ha φ).1, (testMultiplierOn_spec Ω a ha φ).2.1,
    (testMultiplierOn_spec Ω a ha φ).2.2⟩

/-- The transpose `Vᵀφ = -Σⱼ ∂ⱼ(φ Vⱼ)` as a map of test functions on `Ω`. -/
def fieldTransposeTest {n : ℕ} (Ω : Opens (Fin n → ℝ)) (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
  -∑ j : Fin n, TestFunction.lineDerivCLM ℝ (Pi.single j 1)
    (testMultiplierOn Ω (fun x => V x j) ((contDiff_apply ℝ ℝ j).comp_contDiffOn hV) φ)

/-- `T` is a distribution on `Ω` with `Σᵢ Xᵢ²T = f`, `f ∈ L¹_loc(Ω)`: `T(Σᵢ XᵢᵀXᵢᵀφ) = ∫ fφ`. -/
def hasDistributionEquation {q n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume ∧
  ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
    T (∑ i, fieldTransposeTest Ω (X i) (hX i) (fieldTransposeTest Ω (X i) (hX i) φ)) =
      Distribution.ofFun Ω f volume (⊤ : ℕ∞) φ

/-- `T` is a distribution on `Ω` with `X₀T + Σᵢ Xᵢ²T = f`, `f ∈ L¹_loc(Ω)`. -/
def hasDistributionEquationWithDrift {q n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume ∧
  ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
    T (fieldTransposeTest Ω (X 0) (hX 0) φ +
      ∑ i : Fin q, fieldTransposeTest Ω (X i.succ) (hX i.succ)
        (fieldTransposeTest Ω (X i.succ) (hX i.succ) φ)) =
      Distribution.ofFun Ω f volume (⊤ : ℕ∞) φ

/-! ## `X`-Sobolev spaces -/

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

/-- `‖X_I f‖_{Lᵖ(V)}`, the infimum over weak derivatives `g` (`∞` if there is none). -/
def weakWordENorm {m n : ℕ} (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (I : List (Fin m)) (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X V I f g ∧
    AEStronglyMeasurable g (volume.restrict (V : Set (Fin n → ℝ))) ∧
    r = eLpNorm g p (volume.restrict (V : Set (Fin n → ℝ)))}

/-- The norm `‖f‖_{W^{k,p}_X(V)} = Σ_{weight(I) ≤ k} ‖X_I f‖_{Lᵖ(V)}`. -/
def sobolevXENorm {m n : ℕ} (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ I ∈ wordFamily w k, weakWordENorm X V I p f

/-! ## `X`-Hölder spaces -/

/-- `g(x)` is the derivative of `f` along `X` at every `x ∈ V`: there is a local integral curve
of `X` through `x`, and `(f ∘ γ)'(0) = g(x)` along every local integral curve `γ` in `V`. -/
def hasIntrinsicDeriv {n : ℕ} (V : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (f g : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ (V : Set (Fin n → ℝ)),
    (∃ γ : ℝ → (Fin n → ℝ), γ 0 = x ∧ IsIntegralCurveAt γ (fun _ => X) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (V : Set (Fin n → ℝ))) ∧
    ∀ γ : ℝ → (Fin n → ℝ), γ 0 = x → IsIntegralCurveAt γ (fun _ => X) 0 →
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (V : Set (Fin n → ℝ))) →
      HasDerivAt (fun t => f (γ t)) (g x) 0

/-- `g = X_{i₁}(X_{i₂}(⋯ X_{iⱼ} f))` on `V`, iterating `hasIntrinsicDeriv`. -/
def hasIntrinsicWordDeriv {m n : ℕ} (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) :
    List (Fin m) → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ) → Prop
  | [], f, g => EqOn g f (V : Set (Fin n → ℝ))
  | i :: I, f, g => ∃ h : (Fin n → ℝ) → ℝ,
      hasIntrinsicWordDeriv X V I f h ∧ hasIntrinsicDeriv V (X i) h g

/-- The `α`-Hölder seminorm on `V` with respect to `d` (pairs with `d = ∞` are ignored). -/
def holderSeminorm {n : ℕ} (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
    (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {C : ℝ≥0∞ | C < ⊤ ∧ ∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ →
    ENNReal.ofReal |f x - f y| ≤ C * (d x y) ^ α}

/-- The norm `sup_V |f| + [f]_{α,V}`. -/
def holderENorm {n : ℕ} (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
    (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  (⨆ x : V, ENNReal.ofReal |f x|) + holderSeminorm d α V f

/-- `‖X_I f‖_{C^α(V)}`, the infimum over intrinsic derivatives `g` (`∞` if there is none). -/
def intrinsicWordENorm {m n : ℕ} (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (V : Opens (Fin n → ℝ)) (I : List (Fin m))
    (α : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ g : (Fin n → ℝ) → ℝ,
    hasIntrinsicWordDeriv X V I f g ∧ r = holderENorm d α (V : Set (Fin n → ℝ)) g}

/-- The norm `‖f‖_{C^{k,α}_X(V)} = Σ_{weight(I) ≤ k} ‖X_I f‖_{C^α(V)}`. -/
def holderXENorm {m n : ℕ} (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (V : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ I ∈ wordFamily w k, intrinsicWordENorm X d V I α f

/-- `f ∈ C^{k,α}_X(V)`: `f` and its intrinsic derivatives along words of weight `≤ k` have
finite `C^α(V)` norm. -/
def memHolderX {m n : ℕ} (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (V : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  holderENorm d α (V : Set (Fin n → ℝ)) f < ⊤ ∧
  ∀ I ∈ wordFamily w k, ∃ g : (Fin n → ℝ) → ℝ,
    hasIntrinsicWordDeriv X V I f g ∧ holderENorm d α (V : Set (Fin n → ℝ)) g < ⊤

/-- `f ∈ C^{k,α}_{X,loc}(Ω)`: `f ∈ C^{k,α}_X(V)` for every open `V ⋐ Ω`. -/
def memHolderXLoc {m n : ℕ} (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (Ω : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ V : Opens (Fin n → ℝ), IsCompact (closure (V : Set (Fin n → ℝ))) →
    closure (V : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) → memHolderX w X d V k α f

/-- `f ∈ C^{k,α}_X(V)` and `V ∩ {f ≠ 0}` has compact closure inside `V`. -/
def memHolderXCompact {m n : ℕ} (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (V : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  memHolderX w X d V k α f ∧
  IsCompact (closure ((V : Set (Fin n → ℝ)) ∩ Function.support f)) ∧
  closure ((V : Set (Fin n → ℝ)) ∩ Function.support f) ⊆ (V : Set (Fin n → ℝ))

/-! ## The Rothschild–Stein interior estimates -/

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Rothschild–Stein `Lᵖ` estimate** for `ΣXᵢ²` (BB Theorem 11.1(a)). -/
theorem rothschildStein_sobolev {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memSobolevX noDriftWeight X Ω k p f → hasDistributionEquation Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          memSobolevXLoc noDriftWeight X Ω (k + 2) p u ∧
          sobolevXENorm noDriftWeight X V (k + 2) p u ≤
            ENNReal.ofReal C * (sobolevXENorm noDriftWeight X W k p f +
              eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) := by
  exact RothschildStein.rs3_no_drift_sobolev hn hq Ω V W hV hVW hW hWΩ X hX hspan k p hp hp_top

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Rothschild–Stein Hölder estimate** for `ΣXᵢ²` (BB Theorem 11.1(b)). -/
theorem rothschildStein_holder {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let d := controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memHolderX noDriftWeight X d Ω k α f → hasDistributionEquation Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          ContinuousOn u (Ω : Set (Fin n → ℝ)) ∧
          memHolderXLoc noDriftWeight X d Ω (k + 2) α u ∧
          holderXENorm noDriftWeight X d V (k + 2) α u ≤
            ENNReal.ofReal C * (holderXENorm noDriftWeight X d W k α f +
              eLpNorm u ⊤ (volume.restrict (W : Set (Fin n → ℝ)))) ∧
          ∃ g : Fin q → (Fin n → ℝ) → ℝ,
            (∀ i, hasIntrinsicWordDeriv X Ω [i, i] u (g i)) ∧
            (∀ x ∈ (Ω : Set (Fin n → ℝ)), (∑ i, g i x) = f x) := by
  exact RothschildStein.rs3_no_drift_holder hn hq Ω V W hV hVW hW hWΩ X hX hspan k α hα hα1

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Rothschild–Stein `Lᵖ` estimate** for `X₀ + ΣXᵢ²` (BB Theorem 11.2, `k = 0`). -/
theorem rothschildStein_sobolev_drift {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memSobolevX driftWeight X Ω 0 p f → hasDistributionEquationWithDrift Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          memSobolevXLoc driftWeight X Ω 2 p u ∧
          sobolevXENorm driftWeight X V 2 p u ≤
            ENNReal.ofReal C * (sobolevXENorm driftWeight X W 0 p f +
              eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) := by
  exact RothschildStein.rs3_drift_sobolev hn hq Ω V W hV hVW hW hWΩ X hX hspan p hp hp_top

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Rothschild–Stein Hölder estimate** for `X₀ + ΣXᵢ²` (BB Theorem 11.2, `k = 0`). -/
theorem rothschildStein_holder_drift {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let d := controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memHolderX driftWeight X d Ω 0 α f → hasDistributionEquationWithDrift Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          ContinuousOn u (Ω : Set (Fin n → ℝ)) ∧
          memHolderXLoc driftWeight X d Ω 2 α u ∧
          holderXENorm driftWeight X d V 2 α u ≤
            ENNReal.ofReal C * (holderXENorm driftWeight X d W 0 α f +
              eLpNorm u ⊤ (volume.restrict (W : Set (Fin n → ℝ)))) ∧
          ∃ g : Fin (q + 1) → (Fin n → ℝ) → ℝ,
            hasIntrinsicWordDeriv X Ω [0] u (g 0) ∧
            (∀ i : Fin q, hasIntrinsicWordDeriv X Ω [i.succ, i.succ] u (g i.succ)) ∧
            (∀ x ∈ (Ω : Set (Fin n → ℝ)), (∑ i : Fin q, g i.succ x) + g 0 x = f x) := by
  exact RothschildStein.rs3_drift_holder hn hq Ω V W hV hVW hW hWΩ X hX hspan α hα hα1

/-! ## Homogeneous groups and the fundamental solution -/

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

/-- The group inverse `x⁻¹`. -/
def inv (x : Fin N → ℝ) : Fin N → ℝ := fun j => MvPolynomial.eval x (G.inversePolynomial j)

/-- The group dilation `D(t)`. -/
def dilate (t : ℝ) (x : Fin N → ℝ) : Fin N → ℝ := coordinateDilation G.weight t x

/-- The homogeneous dimension `Q = Σⱼ ωⱼ`. -/
def homogeneousDimension : ℕ := ∑ j, G.weight j

/-- The left-invariant field `Zⱼ` equal to `∂ⱼ` at `0`: `Zⱼ(x) = D(y ↦ x ∘ y)(0) eⱼ`. -/
def canonicalField (j : Fin N) (x : Fin N → ℝ) : Fin N → ℝ :=
  fderiv ℝ (G.mul x) 0 (Pi.single j 1)

/-- The drift system: `Z_{q+1}` (as `X₀`) followed by `Z₁, …, Z_q`. -/
def driftFields {q : ℕ} (hq : q + 1 ≤ N) : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ) :=
  Fin.cases (G.canonicalField ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩)
    (fun i : Fin q => G.canonicalField ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩)

/-- The first `q` canonical fields `Z₁, …, Z_q`. -/
def horizontalFields {q : ℕ} (hq : q ≤ N) (i : Fin q) : (Fin N → ℝ) → (Fin N → ℝ) :=
  G.canonicalField (Fin.castLE hq i)

/-- A homogeneous norm: continuous, nonnegative, vanishing only at `0`, `ν(D(t)x) = tν(x)`. -/
def IsHomogeneousGauge (ν : (Fin N → ℝ) → ℝ) : Prop :=
  Continuous ν ∧ (∀ x, 0 ≤ ν x) ∧ (∀ x, ν x = 0 ↔ x = 0) ∧
    (∀ t : ℝ, 0 < t → ∀ x, ν (G.dilate t x) = t * ν x)

/-- `T` is a distribution on `ℝᴺ` homogeneous of degree `a`: `T(φ ∘ D(t)) = t^{-Q-a} T(φ)`. -/
def HasHomogeneousDistribution (degree : ℝ) (T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    Prop :=
  ∀ t : ℝ, 0 < t → ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    ∃ ψ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
      (∀ x, ψ x = φ (G.dilate t x)) ∧
      T ψ = t ^ (-(G.homogeneousDimension : ℝ) - degree) * T φ

/-- The convolution `∫ f(u) K(u⁻¹ ∘ v) du`. -/
def potential (kernel f : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) : ℝ :=
  ∫ u, f u * kernel (G.mul (G.inv u) v)

/-- The principal value `lim_{ε → 0⁺} ∫_{ν(u⁻¹ ∘ v) > ε} f(u) K(u⁻¹ ∘ v) du` exists and equals
`value`, the truncated integrals being absolutely convergent. -/
def HasPrincipalValue (ν kernel f : (Fin N → ℝ) → ℝ) (v : Fin N → ℝ) (value : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε →
    IntegrableOn (fun u => f u * kernel (G.mul (G.inv u) v)) {u | ε < ν (G.mul (G.inv u) v)}
      volume) ∧
  Filter.Tendsto (fun ε : ℝ => ∫ u in {u | ε < ν (G.mul (G.inv u) v)},
      f u * kernel (G.mul (G.inv u) v))
    (nhdsWithin 0 (Ioi 0)) (nhds value)

end HomogeneousGroup

/-- The Euclidean derivative `∂^a f` for a multi-index `a`. -/
def euclideanPartial {N : ℕ} (a : Fin N → ℕ) (f : (Fin N → ℝ) → ℝ) : (Fin N → ℝ) → ℝ :=
  ((List.finRange N).flatMap fun j => List.replicate (a j) j).foldr
    (fun j g x => fderiv ℝ g x (Pi.single j 1)) f

/-- A linear differential operator `Σ_{a ∈ indices} c_a(x) ∂^a` with smooth coefficients. -/
structure SmoothDifferentialOperator (N : ℕ) where
  indices : Finset (Fin N → ℕ)
  coefficient : (Fin N → ℕ) → (Fin N → ℝ) → ℝ
  smooth_coefficient : ∀ a ∈ indices, ContDiff ℝ (⊤ : ℕ∞) (coefficient a)

/-- The action `Df(x) = Σ_a c_a(x) ∂^a f(x)`. -/
def SmoothDifferentialOperator.apply {N : ℕ} (D : SmoothDifferentialOperator N)
    (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ a ∈ D.indices, D.coefficient a x * euclideanPartial a f x

/-- `D` is homogeneous of degree `k`: `D(f ∘ D(t)) = t^k (Df) ∘ D(t)` for smooth `f`. -/
def SmoothDifferentialOperator.IsHomogeneous {N : ℕ} (D : SmoothDifferentialOperator N)
    (G : HomogeneousGroup N) (degree : ℝ) : Prop :=
  ∀ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t : ℝ, 0 < t → ∀ x,
    D.apply (f ∘ G.dilate t) x = t ^ degree * D.apply f (G.dilate t x)

/-- `T` is a fundamental solution of the operator `P` with transpose `Pᵀ`: `T(Pᵀφ) = φ(0)`. -/
def isFundamentalDistribution {N : ℕ}
    (transposeOperator : (((Fin N → ℝ) → ℝ) → ((Fin N → ℝ) → ℝ)))
    (T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) : Prop :=
  ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    ∃ ψ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
      (∀ x, ψ x = transposeOperator φ x) ∧ T ψ = φ 0

/-- `u ∈ L¹_loc(Ω)` represents the distribution `T`. -/
def representsDistribution {n : ℕ} (Ω : Opens (Fin n → ℝ)) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (u : (Fin n → ℝ) → ℝ) : Prop :=
  LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧ T = Distribution.ofFun Ω u volume (⊤ : ℕ∞)

/-- The derivative `Vf(x) = Df(x)·V(x)`. -/
def fieldDerivative {n : ℕ} (V : (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (V x)

/-- `Σᵢ Xᵢ² f`. -/
def sumSquares {q n : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, fieldDerivative (X i) (fieldDerivative (X i) f) x

/-- The transpose `Σᵢ XᵢᵀXᵢᵀ φ` of `Σᵢ Xᵢ²`. -/
def sumSquaresTranspose {q n : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, fieldTranspose (X i) (fieldTranspose (X i) φ) x

/-- `X₀f + Σᵢ Xᵢ² f`. -/
def sumSquaresWithDrift {q n : ℕ} (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fieldDerivative (X 0) f x +
    ∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) f) x

/-- The transpose `X₀ᵀφ + Σᵢ XᵢᵀXᵢᵀ φ` of `X₀ + Σᵢ Xᵢ²`. -/
def sumSquaresWithDriftTranspose {q n : ℕ} (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fieldTranspose (X 0) φ x +
    ∑ i : Fin q, fieldTranspose (X i.succ) (fieldTranspose (X i.succ) φ) x

namespace Bridge

/-- The library copy of a homogeneous group. -/
def HomogeneousGroup.toLib {N : ℕ} (G : HomogeneousGroup N) : RothschildStein.HomogeneousGroup N :=
  ⟨G.dimension_pos, G.weight, G.weight_pos, G.weight_mono, G.productPolynomial,
    G.inversePolynomial, G.zero_left, G.zero_right, G.assoc, G.inverse_left, G.inverse_right,
    G.dilation_product⟩

/-- The library copy of a differential operator. -/
def SmoothDifferentialOperator.toLib {N : ℕ} (D : SmoothDifferentialOperator N) :
    RothschildStein.SmoothDifferentialOperator N :=
  ⟨D.indices, D.coefficient, D.smooth_coefficient⟩

end Bridge

/-- The canonical fields `Z₁, …, Z_q` are smooth (supporting theorem). -/
theorem HomogeneousGroup.horizontalFields_contDiff {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (i : Fin q) : ContDiff ℝ (⊤ : ℕ∞) (G.horizontalFields hq i) := by
  exact RothschildStein.HomogeneousGroup.horizontalFields_contDiff
    (Bridge.HomogeneousGroup.toLib G) hq i

/-- The drift system `Z_{q+1}, Z₁, …, Z_q` is smooth (supporting theorem). -/
theorem HomogeneousGroup.driftFields_contDiff {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q + 1 ≤ N) (i : Fin (q + 1)) : ContDiff ℝ (⊤ : ℕ∞) (G.driftFields hq i) := by
  exact RothschildStein.HomogeneousGroup.driftFields_contDiff
    (Bridge.HomogeneousGroup.toLib G) hq i

/-- The kernel properties of BB Theorem 11.5 for an operator `P = L` or `Lᵀ` with transpose
`Pt`, horizontal fields `Y` and second-order quantities `D2`: `K` represents the unique
fundamental solution `T` of `Pt` (`T(Pt φ) = φ(0)`) homogeneous of degree `2 - Q`; `K` is smooth
off `0` and homogeneous of degree `2 - Q`; `|K| ≲ ν^{2-Q}`, `|YᵢK| ≲ ν^{1-Q}`, `D2 ≲ ν^{-Q}`, and
`|DK| ≲ ν^{2-Q-k}` for every operator `D` homogeneous of degree `k`; `∫_{r<ν<R} DK·Φ(ν) = 0` for
`D` homogeneous of degree two; and for test functions `φ`, `P(φ ∗ K) = φ`, `φ = (Pφ) ∗ K`,
`Yⱼφ = (Pφ) ∗ YⱼK`, and `YᵢYⱼφ = p.v. (Pφ) ∗ YᵢYⱼK + Aᵢⱼ Pφ`, writing
`f ∗ K(v) = ∫ f(u) K(u⁻¹ ∘ v) du`. -/
def HomogeneousGroup.IsHomogeneousFundamentalSolution {N q : ℕ} (G : HomogeneousGroup N)
    (Y : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (P Pt : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ)
    (K : (Fin N → ℝ) → ℝ) (D2 : Fin q → Fin q → (Fin N → ℝ) → ℝ) (A : Fin q → Fin q → ℝ)
    (ν : (Fin N → ℝ) → ℝ) : Prop :=
  ∃ T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ)) T ∧
    isFundamentalDistribution Pt T ∧
    (∀ S : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
      G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ)) S →
      isFundamentalDistribution Pt S → S = T) ∧
    representsDistribution ⊤ T K ∧
    ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ) ∧
    (∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
      K (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * K x) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x : Fin N → ℝ, x ≠ 0 →
      |K x| ≤ C * ν x ^ (2 - (G.homogeneousDimension : ℝ)) ∧
      (∀ i : Fin q, |fieldDerivative (Y i) K x| ≤
        C * ν x ^ (1 - (G.homogeneousDimension : ℝ))) ∧
      (∀ i j : Fin q, D2 i j x ≤ C * ν x ^ (-(G.homogeneousDimension : ℝ)))) ∧
    (∀ (D : SmoothDifferentialOperator N) (k : ℝ), D.IsHomogeneous G k →
      ∃ C : ℝ, 0 < C ∧ ∀ x : Fin N → ℝ, x ≠ 0 →
        |D.apply K x| ≤ C * ν x ^ (2 - (G.homogeneousDimension : ℝ) - k)) ∧
    (∀ (D : SmoothDifferentialOperator N), D.IsHomogeneous G 2 →
      ∀ r R : ℝ, 0 < r → r < R →
      ∀ Φ : ℝ → ℝ, ContinuousOn Φ (Icc r R) →
        IntegrableOn (fun x => D.apply K x * Φ (ν x)) {x | r < ν x ∧ ν x < R} ∧
        (∫ x in {x | r < ν x ∧ ν x < R}, D.apply K x * Φ (ν x)) = 0) ∧
    (∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
      ContDiff ℝ (⊤ : ℕ∞) (G.potential K φ) ∧
      (∀ v, P (G.potential K φ) v = φ v) ∧
      ∀ v : Fin N → ℝ,
        Integrable (fun u => P φ u * K (G.mul (G.inv u) v)) ∧
        φ v = G.potential K (P φ) v ∧
        (∀ j : Fin q,
          Integrable (fun u => P φ u * fieldDerivative (Y j) K (G.mul (G.inv u) v)) ∧
          fieldDerivative (Y j) φ v = G.potential (fieldDerivative (Y j) K) (P φ) v) ∧
        (∀ i j : Fin q,
          G.HasPrincipalValue ν (fieldDerivative (Y i) (fieldDerivative (Y j) K)) (P φ) v
            (fieldDerivative (Y i) (fieldDerivative (Y j) φ) v - A i j * P φ v)))

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Fundamental solution on a homogeneous group** (BB Theorem 11.5, via BB Chapter 6) for
`L = Σᵢ Zᵢ²`, the first `q` canonical fields being of weight one and bracket-generating, `Q ≥ 3`:
for `(K, P) = (Γ, L)` and `(Γ*, Lᵀ)`, `Γ*(x) = Γ(x⁻¹)` (here `Γ* = Γ`), `K` has the properties
`IsHomogeneousFundamentalSolution` with `D2 = |YᵢYⱼK|`, for any homogeneous norm `ν`. -/
theorem fundamental_solution {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (ν : (Fin N → ℝ) → ℝ) (hν : G.IsHomogeneousGauge ν) :
    let X := G.horizontalFields hq
    let Y := X
    let L := sumSquares X
    let Lt := sumSquaresTranspose X
    ∃ Γ Γstar : (Fin N → ℝ) → ℝ,
      (∀ x, Γstar x = Γ (G.inv x)) ∧
      (∀ x, Γstar x = Γ x) ∧
      ((∀ x, G.inv x = -x) → ∀ x, Γstar x = Γ (-x)) ∧
      ∃ a : Bool → Fin q → Fin q → ℝ, ∀ b : Bool,
        let K := if b then Γstar else Γ
        let P := if b then Lt else L
        let Pt := if b then L else Lt
        G.IsHomogeneousFundamentalSolution Y P Pt K
          (fun i j x => |fieldDerivative (Y i) (fieldDerivative (Y j) K) x|) (a b) ν := by
  obtain ⟨Γ, Γs, h₁, h₂, h₃, a, hb⟩ :=
    RothschildStein.rs2a_noDrift (Bridge.HomogeneousGroup.toLib G) hq hqpos hw hQ hspan ν hν
  refine ⟨Γ, Γs, h₁, h₂, h₃, a, fun b => ?_⟩
  obtain ⟨T, t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀⟩ := hb b
  intro K P Pt
  exact ⟨T, t₁, t₂, t₃, t₄, t₅, t₆, t₇,
    fun D k hD => t₈ (Bridge.SmoothDifferentialOperator.toLib D) k hD,
    fun D hD => t₉ (Bridge.SmoothDifferentialOperator.toLib D) hD, t₁₀⟩

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Fundamental solution on a homogeneous group** for `Z₀ + Σᵢ Zᵢ²` (BB Theorem 11.5): as in
`fundamental_solution`, with the drift `Z₀ = Z_{q+1}` of weight two and `D2 = |YᵢYⱼK| + |Z₀K|`. -/
theorem fundamental_solution_drift {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N)
    (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.driftFields hq))
    (ν : (Fin N → ℝ) → ℝ) (hν : G.IsHomogeneousGauge ν) :
    let X := G.driftFields hq
    let Y := fun i : Fin q => X i.succ
    let L := sumSquaresWithDrift X
    let Lt := sumSquaresWithDriftTranspose X
    ∃ Γ Γstar : (Fin N → ℝ) → ℝ,
      (∀ x, Γstar x = Γ (G.inv x)) ∧
      ((∀ x, G.inv x = -x) → ∀ x, Γstar x = Γ (-x)) ∧
      ∃ a : Bool → Fin q → Fin q → ℝ, ∀ b : Bool,
        let K := if b then Γstar else Γ
        let P := if b then Lt else L
        let Pt := if b then L else Lt
        G.IsHomogeneousFundamentalSolution Y P Pt K
          (fun i j x => |fieldDerivative (Y i) (fieldDerivative (Y j) K) x| +
            |fieldDerivative (X 0) K x|) (a b) ν := by
  obtain ⟨Γ, Γs, h₁, h₃, a, hb⟩ :=
    RothschildStein.rs2a_drift (Bridge.HomogeneousGroup.toLib G) hq hqpos hw hw0 hQ hspan ν hν
  refine ⟨Γ, Γs, h₁, h₃, a, fun b => ?_⟩
  obtain ⟨T, t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀⟩ := hb b
  intro K P Pt
  exact ⟨T, t₁, t₂, t₃, t₄, t₅, t₆, t₇,
    fun D k hD => t₈ (Bridge.SmoothDifferentialOperator.toLib D) k hD,
    fun D hD => t₉ (Bridge.SmoothDifferentialOperator.toLib D) hD, t₁₀⟩

/-- The global and local estimates for `L` on a homogeneous group (BB §8.4–§8.6), for fields
`X` with weights `w`, `Lsol U T f` meaning `LT = f` in the sense of distributions on `U`,
`d` the control distance on `ℝᴺ` and `νs` a homogeneous norm; `B` (resp. `H`) are the words of
weight two (resp. one), so `Σ_{I ∈ B} ‖X_I u‖` is the full second-order part. In order: (1) for
`1 < p < ∞`, `u, Lu ∈ Lᵖ` imply `u ∈ W^{2,p}_X(ℝᴺ)`, `Σ_B ‖X_I u‖_p ≤ C‖Lu‖_p` and
`‖u‖_{W^{2,p}} ≤ C(‖Lu‖_p + ‖u‖_p)`; (2) `Σ_B [X_I u]_α ≤ C [Lu]_α` for compactly supported
`u ∈ C^{2,α}_X`; (3) its full-norm version for supports in a `d`-ball of radius `R`; (4) the
scale-invariant local `Lᵖ` estimate on `U = z ∘ {νs < r}`, `V = z ∘ {νs < r/2}`; (5), (6) local
`Lᵖ` and Hölder regularity of distributional solutions on any open `Ω`; (7), (8) interior `Lᵖ`
and Hölder estimates for `A ⋐ V ⋐ Ω`; (9) solvability with `W^{2,p}` bounds on domains in a
`d`-ball of radius `R`; (10) the same with `C^{2,α}` bounds for compactly supported data. -/
def HomogeneousGroup.RegularityEstimates {N a : ℕ} (G : HomogeneousGroup N)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)) (w : Fin a → ℕ+)
    (Lsol : (U : Opens (Fin N → ℝ)) → Distribution U ℝ (⊤ : ℕ∞) → ((Fin N → ℝ) → ℝ) → Prop)
    (νs : (Fin N → ℝ) → ℝ) : Prop :=
  let d := controlDistance univ w X
  let H := (wordFamily w 2).filter (fun I => wordWeight w I = 1)
  let B := (wordFamily w 2).filter (fun I => wordWeight w I = 2)
  (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∃ C : ℝ, 0 < C ∧
    ∀ u f : (Fin N → ℝ) → ℝ,
      MemLp u p volume → MemLp f p volume →
      (∃ T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
        representsDistribution ⊤ T u ∧
        Lsol ⊤ T f) →
      memSobolevX w X ⊤ 2 p u ∧
      (∑ I ∈ B, weakWordENorm X ⊤ I p u) ≤ ENNReal.ofReal C * eLpNorm f p volume ∧
      sobolevXENorm w X ⊤ 2 p u ≤ ENNReal.ofReal C *
        (eLpNorm f p volume + eLpNorm u p volume)) ∧
  (∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, 0 < C ∧
    ∀ u : (Fin N → ℝ) → ℝ, memHolderXCompact w X d ⊤ 2 α u →
      ∃ f : (Fin N → ℝ) → ℝ,
        memHolderX w X d ⊤ 0 α f ∧
        Lsol ⊤
          (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) f ∧
      ∃ g : List (Fin a) → (Fin N → ℝ) → ℝ,
        (∀ I ∈ B, hasIntrinsicWordDeriv X ⊤ I u (g I)) ∧
        (∑ I ∈ B, holderSeminorm d α univ (g I)) ≤
          ENNReal.ofReal C * holderSeminorm d α univ f) ∧
  (∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ, 0 < R →
    ∃ C : ℝ, 0 < C ∧ ∀ z : Fin N → ℝ,
    ∀ u : (Fin N → ℝ) → ℝ, memHolderXCompact w X d ⊤ 2 α u →
      tsupport u ⊆ {x | d z x < ENNReal.ofReal R} →
      ∃ f : (Fin N → ℝ) → ℝ,
        memHolderX w X d ⊤ 0 α f ∧
        Lsol ⊤
          (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) f ∧
        (∑ I ∈ B, intrinsicWordENorm X d ⊤ I α u) ≤
          ENNReal.ofReal C * holderENorm d α univ f) ∧
  (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∃ C : ℝ, 0 < C ∧
    ∀ z : Fin N → ℝ, ∀ r : ℝ, 0 < r →
    ∀ U V : Opens (Fin N → ℝ),
      (∀ x, x ∈ U ↔ νs (G.mul (G.inv z) x) < r) →
      (∀ x, x ∈ V ↔ νs (G.mul (G.inv z) x) < r / 2) →
    ∀ u : (Fin N → ℝ) → ℝ, memSobolevX w X U 2 p u →
      ∃ f : (Fin N → ℝ) → ℝ,
        MemLp f p (volume.restrict (U : Set (Fin N → ℝ))) ∧
        Lsol U
          (Distribution.ofFun U u volume (⊤ : ℕ∞)) f ∧
        (∑ I ∈ B, weakWordENorm X V I p u) +
          ENNReal.ofReal (r⁻¹) * (∑ I ∈ H, weakWordENorm X V I p u) +
          ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (V : Set (Fin N → ℝ))) ≤
        ENNReal.ofReal C * (eLpNorm f p (volume.restrict (U : Set (Fin N → ℝ))) +
          ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (U : Set (Fin N → ℝ))))) ∧
  (∀ p : ℝ≥0∞, 1 < p → p < ⊤ →
    ∀ Ω : Opens (Fin N → ℝ),
    ∀ T : Distribution Ω ℝ (⊤ : ℕ∞), ∀ f : (Fin N → ℝ) → ℝ,
      memSobolevXLoc w X Ω 0 p f →
      Lsol Ω T f →
      ∃ u : (Fin N → ℝ) → ℝ, representsDistribution Ω T u ∧
        memSobolevXLoc w X Ω 2 p u) ∧
  (∀ α : ℝ, 0 < α → α < 1 →
    ∀ Ω : Opens (Fin N → ℝ),
    ∀ T : Distribution Ω ℝ (⊤ : ℕ∞), ∀ f : (Fin N → ℝ) → ℝ,
      memHolderXLoc w X d Ω 0 α f →
      Lsol Ω T f →
      ∃ u : (Fin N → ℝ) → ℝ, representsDistribution Ω T u ∧
        memHolderXLoc w X d Ω 2 α u) ∧
  (∀ p : ℝ≥0∞, 1 < p → p < ⊤ →
    ∀ Ω A V : Opens (Fin N → ℝ),
      IsCompact (closure (A : Set (Fin N → ℝ))) →
      closure (A : Set (Fin N → ℝ)) ⊆ (V : Set (Fin N → ℝ)) →
      IsCompact (closure (V : Set (Fin N → ℝ))) →
      closure (V : Set (Fin N → ℝ)) ⊆ (Ω : Set (Fin N → ℝ)) →
    ∃ C : ℝ, 0 < C ∧ ∀ u f : (Fin N → ℝ) → ℝ,
      memSobolevXLoc w X Ω 2 p u →
      Lsol Ω
        (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f →
      MemLp f p (volume.restrict (V : Set (Fin N → ℝ))) →
      sobolevXENorm w X A 2 p u ≤ ENNReal.ofReal C *
        (eLpNorm f p (volume.restrict (V : Set (Fin N → ℝ))) +
         eLpNorm u p (volume.restrict (V : Set (Fin N → ℝ))))) ∧
  (∀ α : ℝ, 0 < α → α < 1 →
    ∀ Ω A V : Opens (Fin N → ℝ),
      IsCompact (closure (A : Set (Fin N → ℝ))) →
      closure (A : Set (Fin N → ℝ)) ⊆ (V : Set (Fin N → ℝ)) →
      IsCompact (closure (V : Set (Fin N → ℝ))) →
      closure (V : Set (Fin N → ℝ)) ⊆ (Ω : Set (Fin N → ℝ)) →
    ∃ C : ℝ, 0 < C ∧ ∀ u f : (Fin N → ℝ) → ℝ,
      memHolderXLoc w X d Ω 2 α u →
      Lsol Ω
        (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f →
      holderENorm d α (V : Set (Fin N → ℝ)) f < ⊤ →
      holderXENorm w X d A 2 α u ≤ ENNReal.ofReal C *
        (holderENorm d α (V : Set (Fin N → ℝ)) f +
          ⨆ x : V, ENNReal.ofReal |u x|)) ∧
  (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∀ R : ℝ, 0 < R →
    ∃ C : ℝ, 0 < C ∧ ∀ Ω : Opens (Fin N → ℝ),
      (Ω : Set (Fin N → ℝ)) ⊆ {x | d 0 x < ENNReal.ofReal R} →
    ∀ f : (Fin N → ℝ) → ℝ, MemLp f p (volume.restrict (Ω : Set (Fin N → ℝ))) →
      ∃ u : (Fin N → ℝ) → ℝ, memSobolevX w X Ω 2 p u ∧
        Lsol Ω
          (Distribution.ofFun Ω u volume (⊤ : ℕ∞)) f ∧
        sobolevXENorm w X Ω 2 p u ≤ ENNReal.ofReal C *
          eLpNorm f p (volume.restrict (Ω : Set (Fin N → ℝ)))) ∧
  (∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ, 0 < R →
    ∃ S : ℝ, R < S ∧ ∃ V : Opens (Fin N → ℝ),
      (∀ x, x ∈ V ↔ νs x < S) ∧
      {x | d 0 x < ENNReal.ofReal R} ⊆ (V : Set (Fin N → ℝ)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ Ω : Opens (Fin N → ℝ),
      (Ω : Set (Fin N → ℝ)) ⊆ {x | d 0 x < ENNReal.ofReal R} →
    ∀ f : (Fin N → ℝ) → ℝ, memHolderXCompact w X d Ω 0 α f →
      (∀ x ∉ Ω, f x = 0) →
      ∃ u : (Fin N → ℝ) → ℝ, memHolderX w X d V 2 α u ∧
        Lsol V
          (Distribution.ofFun V u volume (⊤ : ℕ∞)) f ∧
        holderXENorm w X d V 2 α u ≤ ENNReal.ofReal C * holderENorm d α univ f)

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Global estimates on a homogeneous group** for `Σ Zᵢ²` (BB §8.4–§8.6), in the setting of
`fundamental_solution`, with a homogeneous norm `νs` smooth off `0` and symmetric. -/
theorem global_estimates {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (hνs_symm : ∀ x, νs (G.inv x) = νs x) :
    G.RegularityEstimates (G.horizontalFields hq) noDriftWeight
      (fun U T f => hasDistributionEquation U (G.horizontalFields hq)
        (fun i => (G.horizontalFields_contDiff hq i).contDiffOn) T f) νs := by
  exact RothschildStein.rs2b_noDrift (Bridge.HomogeneousGroup.toLib G) hq hqpos hw hQ hspan νs hνs
    hνs_smooth hνs_symm

-- Recursive definitions are compared with the library copies by unfolding them.
set_option smartUnfolding false in
/-- **Global estimates on a homogeneous group** for `Z₀ + Σ Zᵢ²` (BB §8.4–§8.6), in the setting
of `fundamental_solution_drift`, with a homogeneous norm `νs` smooth off `0` and symmetric. -/
theorem global_estimates_drift {N q : ℕ} (G : HomogeneousGroup N) (hq : q + 1 ≤ N)
    (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (hνs_symm : ∀ x, νs (G.inv x) = νs x) :
    G.RegularityEstimates (G.driftFields hq) driftWeight
      (fun U T f => hasDistributionEquationWithDrift U (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn) T f) νs := by
  exact RothschildStein.rs2b_drift (Bridge.HomogeneousGroup.toLib G) hq hqpos hw hw0 hQ hspan νs
    hνs hνs_smooth hνs_symm

end RothschildSteinChallenge

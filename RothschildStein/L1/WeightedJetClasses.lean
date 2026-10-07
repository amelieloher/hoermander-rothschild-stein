-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.Definitions.WeightedJet
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.L1

/-- Forbidden ordinary partial jets through degree p, with a real
weighted-degree threshold. Smoothness is supplied by the jet class. -/
def scalarJetVanishing {N : ℕ} (ω : Fin N → ℕ) (a : ℝ) (p : ℕ)
    (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ J : List (Fin N), J.length ≤ p → (((J.map ω).sum : ℕ) : ℝ) < a → rsPartial J f 0 = 0

/-- The coefficient of coordinate j has threshold a + ω j. -/
def fieldJetVanishing {N : ℕ} (ω : Fin N → ℕ) (a : ℝ) (p : ℕ)
    (R : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ j, scalarJetVanishing ω (a + ω j) p (fun u => R u j)

/-- Smooth scalar weighted jet class F_a^p. -/
def scalarJetClass {N : ℕ} (Ω : Set (Fin N → ℝ)) (ω : Fin N → ℕ)
    (a : ℝ) (p : ℕ) (f : (Fin N → ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧ scalarJetVanishing ω a p f

/-- Smooth field weighted jet class V_a^p. -/
def fieldJetClass {N : ℕ} (Ω : Set (Fin N → ℝ)) (ω : Fin N → ℕ)
    (a : ℝ) (p : ℕ) (R : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) R Ω ∧ fieldJetVanishing ω a p R

/-- Circle means zero value at the chart origin. -/
def circleScalarJetClass {N : ℕ} (Ω : Set (Fin N → ℝ)) (ω : Fin N → ℕ)
    (a : ℝ) (p : ℕ) (f : (Fin N → ℝ) → ℝ) : Prop :=
  scalarJetClass Ω ω a p f ∧ f 0 = 0

/-- The circle field class has zero vector value at the origin. -/
def circleFieldJetClass {N : ℕ} (Ω : Set (Fin N → ℝ)) (ω : Fin N → ℕ)
    (a : ℝ) (p : ℕ) (R : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  fieldJetClass Ω ω a p R ∧ R 0 = 0

/-- Full field weight is membership at every ordinary jet degree. -/
def fullFieldJetClass {N : ℕ} (Ω : Set (Fin N → ℝ)) (ω : Fin N → ℕ)
    (a : ℝ) (R : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ p, fieldJetClass Ω ω a p R

/-- The Euler operator from BB (10.25), p. 505. -/
def jetEulerOperator {N : ℕ} (R : (Fin N → ℝ) → (Fin N → ℝ))
    (u : Fin N → ℝ) : Fin N → ℝ :=
  (2 : ℝ) • R u + ∑ j, u j • VectorField.lieBracket ℝ (fun _ => Pi.single j 1) R u

/-- Lowering the threshold or the ordinary degree preserves vanishing. -/
theorem scalarJetVanishing_mono {N p q : ℕ} {ω : Fin N → ℕ} {a b : ℝ}
    {f : (Fin N → ℝ) → ℝ} (h : scalarJetVanishing ω a p f)
    (hba : b ≤ a) (hqp : q ≤ p) : scalarJetVanishing ω b q f :=
  fun J hJ hw => h J (le_trans hJ hqp) (lt_of_lt_of_le hw hba)

/-- The field filtration is monotone in both indices. -/
theorem fieldJetVanishing_mono {N p q : ℕ} {ω : Fin N → ℕ} {a b : ℝ}
    {R : (Fin N → ℝ) → (Fin N → ℝ)} (h : fieldJetVanishing ω a p R)
    (hba : b ≤ a) (hqp : q ≤ p) : fieldJetVanishing ω b q R :=
  fun j => scalarJetVanishing_mono (h j) (by linarith) hqp

/-- Integer full weights match the exact remainder predicate `WeightedJet`. -/
theorem fieldJetVanishing_all_iff_WeightedJet {N : ℕ} (ω : Fin N → ℕ)
    (a : ℤ) (R : (Fin N → ℝ) → (Fin N → ℝ)) :
    (∀ p, fieldJetVanishing ω (a : ℝ) p R) ↔ WeightedJet ω a R := by
  constructor
  · intro h j J hJ
    have hi : (((J.map ω).sum : ℕ) : ℤ) < a + (ω j : ℤ) := by
      simpa only [Nat.cast_list_sum] using hJ
    have hr := (Int.cast_lt (R := ℝ)).mpr hi
    exact h J.length j J le_rfl (by simpa only [Int.cast_natCast,Int.cast_add] using hr)
  · intro h p j J _ hJ
    have hr : ((((J.map ω).sum : ℕ) : ℤ) : ℝ) < ((a + (ω j : ℤ) : ℤ) : ℝ) := by
      simpa only [Int.cast_natCast,Int.cast_add] using hJ
    have hi := (Int.cast_lt (R := ℝ)).mp hr
    exact h j J (by simpa only [Nat.cast_list_sum] using hi)
end RothschildStein.L1

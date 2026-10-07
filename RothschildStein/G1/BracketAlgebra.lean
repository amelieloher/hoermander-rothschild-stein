-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Words
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.fieldDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- The field bracket acts as the commutator on smooth scalar functions
(BB Def 1.4 and (1.6), p. 4). -/
theorem bracket_derivative {N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    {U V : (Fin N → ℝ) → (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    fieldDerivative (VectorField.lieBracket ℝ U V) f x =
      fieldDerivative U (fieldDerivative V f) x -
        fieldDerivative V (fieldDerivative U f) x := by
  exact VectorField.fderiv_apply_lieBracket
    (hf.contDiffAt (hΩ.mem_nhds hx)) (by simp)
    ((hV.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    ((hU.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))

/-- Standard brackets retain local smoothness (BB pp. 10–12). -/
theorem wordBracket_contDiffOn {m N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (I : List (Fin m)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wordBracket X I) Ω := by
  induction I with
  | nil => exact contDiffOn_const
  | cons i I ih =>
      cases I with
      | nil => exact hX i
      | cons j I =>
          apply hΩ.contDiffOn_iff.mpr
          intro x hx
          exact (hX i |>.contDiffAt (hΩ.mem_nhds hx)).lieBracket_vectorField
            (ih.contDiffAt (hΩ.mem_nhds hx)) (by simp)

/-- The letters of the existing right-nested word carrier (BB Def 1.17, p. 10). -/
def nestedLetters {k : ℕ} : Hormander.C.NestedWord k → List (Fin (k + 1))
  | .generator i => [i]
  | .bracket i u => i :: nestedLetters u

/-- Right-nested words are nonempty (BB Def 1.17, p. 10). -/
theorem nestedLetters_ne_nil {k : ℕ} (u : Hormander.C.NestedWord k) : nestedLetters u ≠ [] := by
  cases u <;> simp [nestedLetters]

/-- The normalized word evaluates to its right-nested Lie bracket (BB p. 10). -/
theorem nestedEval_eq_wordBracket {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (u : Hormander.C.NestedWord k) :
    Hormander.C.nestedEval X u = wordBracket X (nestedLetters u) := by
  induction u with
  | generator i => rfl
  | bracket i u ih =>
      rw [Hormander.C.nestedEval, ih]
      cases u <;> rfl

/-- The additive weight of a binary expression (BB Lemma 1.21, p. 12). -/
def binaryWeight {k : ℕ} (w : Fin (k + 1) → ℕ+) : Hormander.Interface.LieWord k → ℕ
  | .generator i => w i
  | .bracket p q => binaryWeight w p + binaryWeight w q

/-- Local smooth fields are closed under the bracket (BB Prop 1.11, p. 8). -/
theorem bracket_contDiffOn {N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    {U V : (Fin N → ℝ) → (Fin N → ℝ)}
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (VectorField.lieBracket ℝ U V) Ω := by
  apply hΩ.contDiffOn_iff.mpr
  intro x hx
  exact (hU.contDiffAt (hΩ.mem_nhds hx)).lieBracket_vectorField
    (hV.contDiffAt (hΩ.mem_nhds hx)) (by simp)

end RothschildStein.G1

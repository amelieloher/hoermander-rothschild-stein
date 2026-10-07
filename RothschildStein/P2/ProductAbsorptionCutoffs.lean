-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.ProductAbsorptionSingle
public import RothschildStein.P2.Cutoffs
public import RothschildStein.P1.BracketExpansion
public import RothschildStein.S.HolderListSums
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.FieldDerivativeListSum
public import RothschildStein.Definitions.sumSquaresWithDrift

/-!
# The cutoff family `{ζ, X̃_l ζ, L̃ ζ}` satisfies the hypotheses of the common absorption

Part of the product absorption estimate. The bounds of the radial cutoff construction (`‖X̃_I ζ‖_∞ ≤ C_I a^{-wt I}` and
`‖X̃_I ζ‖_{C^α} ≤ C_I a^{-(wt I + 1)}`, `a = r - s`) for the radial cutoff `ζ` give, for the
family `{ζ, X̃_l ζ (1 ≤ l ≤ q), L̃ ζ}` of weights `d_b = 0, 1, 2`, exactly the hypotheses
`CutoffBounds` of `ProductAbsorptionSingle` with one constant `C_b`:
`X̃_I (X̃_l ζ) = X̃_{I l} ζ` and `X̃_I (L̃ ζ) = ∑ X̃_{I w} ζ` over the `q + 1` words `w` of
weight two (`[0]`, `[i, i]`), the sums being linear on the open patch where the fields are
smooth. The Hölder norms transfer from the lifted control distance of the chart domain to the
control distance of a smaller open set `Ωt ⊆ C.O` (a larger distance gives a smaller seminorm,
`holderENorm_controlDistance_mono`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P2

open RothschildStein.P1

variable {N q : ℕ}

/-- The conclusions of the radial cutoff construction for one cutoff `ζ` at the scale `a`, with the word constants
`c I` (`‖X̃_I ζ‖_∞ ≤ c_I a^{-wt I}`, `‖X̃_I ζ‖_{C^α(O)} ≤ c_I a^{-(wt I + 1)}`). -/
structure RadialCutoffBounds (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (O : Set (Fin N → ℝ))
    (α a : ℝ) (ζ : (Fin N → ℝ) → ℝ) (c : List (Fin (q + 1)) → ℝ) : Prop where
  nonneg : ∀ I, 0 ≤ c I
  sup : ∀ I ξ, |wordDerivative X I ζ ξ| ≤ c I * a ^ (-(wordWeight driftWeight I : ℤ))
  holder : ∀ I, holderENorm (controlDistance O driftWeight X) α O (wordDerivative X I ζ) ≤
    ENNReal.ofReal (c I * a ^ (-((wordWeight driftWeight I : ℤ) + 1)))

/-- Word derivatives are linear for finite list sums on an open set where the fields and the terms
are smooth. -/
theorem wordDerivative_listSum_eqOn {m : ℕ} (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (V : Opens (Fin N → ℝ)) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin N → ℝ)))
    {A : Type*} (items : List A) (g : A → (Fin N → ℝ) → ℝ)
    (hg : ∀ a ∈ items, ContDiffOn ℝ (⊤ : ℕ∞) (g a) (V : Set (Fin N → ℝ))) (I : List (Fin m)) :
    EqOn (wordDerivative X I (fun x => (items.map fun a => g a x).sum))
      (fun x => (items.map fun a => wordDerivative X I (g a) x).sum) (V : Set (Fin N → ℝ)) := by
  induction I with
  | nil => intro x _; rfl
  | cons i J ih =>
    intro z hz
    have hev : wordDerivative X J (fun x => (items.map fun a => g a x).sum) =ᶠ[𝓝 z]
        (fun x => (items.map fun a => wordDerivative X J (g a) x).sum) :=
      Filter.eventually_of_mem (V.isOpen.mem_nhds hz) ih
    have hd : ∀ a ∈ items, DifferentiableAt ℝ (wordDerivative X J (g a)) z := fun a ha =>
      ((S.contDiffOn_wordDerivative V X hX J (g a) (hg a ha)).contDiffAt
        (V.isOpen.mem_nhds hz)).differentiableAt (by simp)
    show fieldDerivative (X i) (wordDerivative X J (fun x => (items.map fun a => g a x).sum)) z =
      (items.map fun a => fieldDerivative (X i) (wordDerivative X J (g a)) z).sum
    unfold fieldDerivative
    rw [hev.fderiv_eq]
    exact S.fieldDerivative_listSum (X i) items (fun a => wordDerivative X J (g a)) z hd

theorem wordWeight_append_eq {m : ℕ} (w : Fin m → ℕ+) (σ τ : List (Fin m)) :
    wordWeight w (σ ++ τ) = wordWeight w σ + wordWeight w τ := by
  simp [wordWeight]

/-- The two kinds of words of weight two: `[0]` and `[i, i]` for `i ≥ 1`. -/
def weightTwoWord (i : Fin (q + 1)) : List (Fin (q + 1)) := if i = 0 then [0] else [i, i]

theorem wordWeight_weightTwoWord (i : Fin (q + 1)) :
    wordWeight driftWeight (weightTwoWord i) = 2 := by
  by_cases hi : i = 0
  · subst hi
    simp [weightTwoWord, wordWeight, driftWeight]
  · simp [weightTwoWord, hi, wordWeight, driftWeight]

theorem weightTwoWord_length (i : Fin (q + 1)) : (weightTwoWord i).length ≤ 2 := by
  by_cases hi : i = 0 <;> simp [weightTwoWord, hi]

/-- `L̃ ζ` is the sum of `X̃_w ζ` over the `q + 1` words of weight two. -/
theorem sumSquaresWithDrift_eq_listSum (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (ζ : (Fin N → ℝ) → ℝ) :
    sumSquaresWithDrift X ζ =
      fun x => ((List.finRange (q + 1)).map fun i => wordDerivative X (weightTwoWord i) ζ x).sum := by
  funext x
  rw [← Fin.sum_univ_def, Fin.sum_univ_succ]
  simp [sumSquaresWithDrift, weightTwoWord, wordDerivative, Fin.succ_ne_zero]

/-- Word derivatives of a function vanish at points outside its topological support. -/
theorem wordDerivative_eq_zero_of_notMem_tsupport {m : ℕ} (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (ζ : (Fin N → ℝ) → ℝ) (I : List (Fin m)) {z : Fin N → ℝ} (hz : z ∉ tsupport ζ) :
    wordDerivative X I ζ z = 0 := by
  have key : ∀ I : List (Fin m), ∀ y ∈ (tsupport ζ)ᶜ, wordDerivative X I ζ y = 0 := by
    intro I
    induction I with
    | nil => intro y hy; exact image_eq_zero_of_notMem_tsupport hy
    | cons i J ih =>
      intro y hy
      have hev : wordDerivative X J ζ =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem ((isClosed_tsupport ζ).isOpen_compl.mem_nhds hy) ih
      show fieldDerivative (X i) (wordDerivative X J ζ) y = 0
      unfold fieldDerivative
      rw [hev.fderiv_eq]
      simp
  exact key I z hz

theorem tsupport_sumSquaresWithDrift_subset (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (ζ : (Fin N → ℝ) → ℝ) : tsupport (sumSquaresWithDrift X ζ) ⊆ tsupport ζ := by
  refine closure_minimal ?_ (isClosed_tsupport ζ)
  intro x hx
  by_contra hnot
  apply hx
  have h0 : ∀ I : List (Fin (q + 1)), wordDerivative X I ζ x = 0 := fun I =>
    wordDerivative_eq_zero_of_notMem_tsupport X ζ I hnot
  rw [sumSquaresWithDrift_eq_listSum]
  simp [h0]

/-- Word derivatives of `L̃ ζ` on the open patch of smoothness. -/
theorem wordDerivative_sumSquaresWithDrift (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (V : Opens (Fin N → ℝ)) (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin N → ℝ)))
    {ζ : (Fin N → ℝ) → ℝ} (hζ : ContDiffOn ℝ (⊤ : ℕ∞) ζ (V : Set (Fin N → ℝ)))
    (I : List (Fin (q + 1))) {z : Fin N → ℝ} (hz : z ∈ (V : Set (Fin N → ℝ))) :
    wordDerivative X I (sumSquaresWithDrift X ζ) z =
      ∑ i : Fin (q + 1), wordDerivative X (I ++ weightTwoWord i) ζ z := by
  rw [sumSquaresWithDrift_eq_listSum]
  refine (wordDerivative_listSum_eqOn X V hXV (List.finRange (q + 1))
      (fun i => wordDerivative X (weightTwoWord i) ζ)
      (fun i _ => S.contDiffOn_wordDerivative V X hXV (weightTwoWord i) ζ hζ) I hz).trans ?_
  beta_reduce
  rw [← Fin.sum_univ_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [wordDerivative_append]

end RothschildStein.P2

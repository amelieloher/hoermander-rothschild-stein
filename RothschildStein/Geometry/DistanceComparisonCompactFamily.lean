-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.bracketStepOn
public import RothschildStein.Definitions.controlDistance
public import RothschildStein.Definitions.rsBall
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.wordWeight
public import RothschildStein.Definitions.absoluteJacobian
public import RothschildStein.Definitions.wordFamily
public import RothschildStein.Geometry.ParameterLocalDistanceComparison
public import RothschildStein.Geometry.WordFamilyDistance
public import RothschildStein.G4.FinitePositiveMinimum

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.Geometry

theorem exists_distance_comparison_compact_family
    {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg]
    {k n s : ℕ} (hn : 0 < n)
    (w : Fin (k + 1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
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
  classical
  intro e ws
  have hVint : V ⊆ interior Ω := by simpa only [hΩ.interior_eq] using hVΩ
  have hs : 1 ≤ s := (w (0 : Fin (k+1))).pos.trans_le (hw 0)
  choose U hU hz C_eq ε hC_eq hε hlocal using
    (fun x : K => exists_parameter_local_distance_comparison hn hs w hw
      hV (hVint.trans interior_subset) X hX hstep hjoint (hKV x.property))
  obtain ⟨T, hcover⟩ := hK.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hz ⟨x, hx⟩⟩)
  obtain ⟨a, ha, haε⟩ := G4.exists_finite_positive_lower_bound T ε (fun i _ => hε i)
  let A := 1 + ∑ i ∈ T, C_eq i
  have hA : 0 < A := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ T) => (hC_eq i).le)
    dsimp [A]; linarith
  refine ⟨A, a, hA, ha, ?_⟩
  intro σ x hx y hd
  have heq : controlDistance Ω ws (fun j => wordBracket (X σ) (e j)) x y =
      G4.auxiliaryDistance (s := s) Ω w (X σ) x y :=
    wordFamily_controlDistance_eq_auxiliaryDistance Ω w (X σ) x y
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨hiT, hiU⟩ := mem_iUnion.mp hi
  have hdaux : G4.auxiliaryDistance (s := s) Ω w (X σ) x y < ENNReal.ofReal (ε i) := by
    rw [← heq]
    exact hd.trans_le (ENNReal.ofReal_le_ofReal (haε i hiT))
  have hc := hlocal i σ x hiU y hdaux
  have hAi : C_eq i ≤ A := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ T) => (hC_eq j).le) hiT
    dsimp [A]; linarith
  rw [heq]
  exact ⟨hc.1, hc.2.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hAi) _)⟩

end RothschildStein.Geometry

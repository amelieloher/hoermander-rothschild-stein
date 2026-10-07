-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.RealHypoellipticity
public import RothschildStein.G1.RankEquivalence
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.hasDistributionEquation
public import RothschildStein.Definitions.hasDistributionEquationWithDrift
public import RothschildStein.S.Transposes

/-!
# The distributional hypoellipticity bridge

The homogeneous hypoellipticity statement (`P T = 0` forces smoothness, BB p. 609) is the zero-forcing
specialization of the hypoellipticity theorem for distributions
(`RothschildStein.Distribution.exists_real_smooth_representative_of_distribution_equation`):
coefficient `c = 0`, forcing `g = 0`. The only new ingredients are

* the bridge from the standard-word rank condition `bracketSpansOn` to the Hörmander
  interface's `LieAlgebraSpansOn` (binary Lie words), and
* for the no-drift equation `hasDistributionEquation` (fields `Fin q`), the augmentation by the zero
  drift field `Fin.cons 0 X : Fin (q + 1) → …`, which leaves both the rank condition and the
  transposed operator unchanged.

The conclusion is stated globally on the open set `Ω`, which contains the local statement
"near each point `T` is the distribution of a smooth real function".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P2

/-- The two coordinate Lie-word evaluations agree. -/
private theorem lieWordEval_eq_eval {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (t : Hormander.Interface.LieWord k) :
    Hormander.lieWordEval X t = Hormander.Interface.LieWord.eval X t := by
  induction t with
  | generator i => rfl
  | bracket a b ha hb =>
    simp only [Hormander.lieWordEval, Hormander.Interface.LieWord.eval, ha, hb]

/-- The standard-word rank condition gives the Hörmander interface's
Lie-word spanning condition (BB Def 1.22, p. 12, through `G1.binary_span_eq_word_span`). -/
theorem lieAlgebraSpansOn_of_bracketSpansOn {k N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin N → ℝ)) X) :
    Hormander.Interface.LieAlgebraSpansOn (Ω : Set (Fin N → ℝ)) X := by
  intro x hx
  have h := G1.binary_span_eq_word_span Ω.isOpen X hX hx
  rw [hspan x hx] at h
  rw [← h]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, (congrFun (lieWordEval_eq_eval X t) x).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, (congrFun (lieWordEval_eq_eval X t) x).symm⟩

/-- The no-drift family `X : Fin q → …` extended by the zero field at the drift index. -/
def zeroDrift {q n : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) :
    Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ) :=
  Fin.cons 0 X

theorem zeroDrift_contDiffOn {q n : ℕ} {s : Set (Fin n → ℝ)}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) s) :
    ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (zeroDrift X i) s := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz : zeroDrift X 0 = 0 := Fin.cons_zero _ _
    rw [hz]
    exact contDiffOn_const
  · simpa [zeroDrift] using hX j

/-- Words in the shifted alphabet evaluate as in the original one. -/
theorem wordBracket_zeroDrift_map_succ {q n : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) :
    ∀ I : List (Fin q), wordBracket (zeroDrift X) (I.map Fin.succ) = wordBracket X I
  | [] => rfl
  | [i] => by simp [wordBracket, zeroDrift]
  | i :: j :: I => by
    have ih := wordBracket_zeroDrift_map_succ X (j :: I)
    simp only [List.map_cons, wordBracket] at ih ⊢
    rw [ih]
    simp [zeroDrift]

/-- The zero-drift augmentation preserves the standard-word rank condition. -/
theorem bracketSpansOn_zeroDrift {q n : ℕ} {Ω : Set (Fin n → ℝ)}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} (hspan : bracketSpansOn Ω X) :
    bracketSpansOn Ω (zeroDrift X) := by
  intro x hx
  apply top_unique
  rw [← hspan x hx]
  apply Submodule.span_mono
  rintro v ⟨I, hI, rfl⟩
  refine ⟨I.map Fin.succ, by simpa using hI, ?_⟩
  rw [wordBracket_zeroDrift_map_succ]

/-- The zero field has zero transpose test. -/
theorem fieldTransposeTest_zero {n : ℕ} (Ω : Opens (Fin n → ℝ))
    (h0 : ContDiffOn ℝ (⊤ : ℕ∞) (0 : (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : fieldTransposeTest Ω 0 h0 φ = 0 := by
  apply TestFunction.ext
  intro x
  rw [S.fieldTransposeTest_apply]
  simp [fieldTranspose, Hormander.Interface.euclideanDivergence]

/-- The zero-drift augmentation has the same transposed operator on tests. -/
theorem sumSquaresWithDriftTransposeTest_zeroDrift {q n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    sumSquaresWithDriftTransposeTest Ω (zeroDrift X) (zeroDrift_contDiffOn hX) φ =
      sumSquaresTransposeTest Ω X hX φ := by
  have h0 : fieldTransposeTest Ω (zeroDrift X 0) (zeroDrift_contDiffOn hX 0) φ = 0 := by
    have hz : zeroDrift X 0 = 0 := Fin.cons_zero _ _
    have := fieldTransposeTest_zero Ω contDiffOn_const φ
    convert this using 2
  unfold sumSquaresWithDriftTransposeTest sumSquaresTransposeTest
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp [zeroDrift]

/-- Applying the scalar transpose twice is the iterated divergence of the interface adjoint. -/
theorem fieldTranspose_fieldTranspose {n : ℕ} (V : (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    fieldTranspose V (fieldTranspose V φ) x =
      Hormander.Interface.euclideanDivergence (fun y =>
        Hormander.Interface.euclideanDivergence (fun q => φ q • V q) y • V y) x := by
  unfold fieldTranspose Hormander.Interface.euclideanDivergence
  simp [neg_smul, fderiv_fun_neg]

/-- The interface adjoint with zero coefficient is the transposed test operator. -/
theorem adjointTest_zero_eq {q n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) (0 : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Distribution.adjointTest Ω X 0 hX hc ψ = sumSquaresWithDriftTransposeTest Ω X hX ψ := by
  apply TestFunction.ext
  intro x
  rw [Distribution.adjointTest_apply]
  unfold sumSquaresWithDriftTransposeTest
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun χ => χ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change _ = ev (_ + ∑ i : Fin q, _)
  rw [map_add, map_sum]
  change _ = (fieldTransposeTest Ω (X 0) (hX 0) ψ : (Fin n → ℝ) → ℝ) x + _
  rw [S.fieldTransposeTest_apply]
  unfold Hormander.Interface.hormanderAdjointTest
  simp only [Pi.zero_apply, zero_mul, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change _ = (fieldTransposeTest Ω (X i.succ) (hX i.succ)
    (fieldTransposeTest Ω (X i.succ) (hX i.succ) ψ) : (Fin n → ℝ) → ℝ) x
  rw [S.fieldTransposeTest_apply, S.fieldTransposeTest_coe, fieldTranspose_fieldTranspose]

/-- Dimension zero: every real distribution on an open subset of the one-point space is given by
a constant function (so the homogeneous hypoellipticity statement needs no positive-dimension hypothesis). -/
theorem exists_smooth_representative_of_dim_zero (Ω : Opens (Fin 0 → ℝ))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) :
    ∃ u : (Fin 0 → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (Ω : Set (Fin 0 → ℝ)) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * u x := by
  have hsub : ∀ x y : Fin 0 → ℝ, x = y := fun x y => Subsingleton.elim x y
  by_cases h : (0 : Fin 0 → ℝ) ∈ (Ω : Set (Fin 0 → ℝ))
  · let φ₁ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
      ⟨fun _ => 1, contDiff_const,
        Set.Subsingleton.isCompact (Set.subsingleton_of_subsingleton),
        fun x _ => by rwa [hsub x 0]⟩
    refine ⟨fun _ => T φ₁, contDiffOn_const, fun ψ => ?_⟩
    have hdec : ψ = ψ 0 • φ₁ := by
      apply TestFunction.ext
      intro x
      rw [hsub x 0]
      change ψ 0 = ψ 0 * 1
      rw [mul_one]
    have hT : T ψ = ψ 0 * T φ₁ := by
      rw [← smul_eq_mul, ← map_smul, ← hdec]
    rw [hT, Measure.volume_pi_eq_dirac 0, integral_dirac]
  · refine ⟨fun _ => 0, contDiffOn_const, fun ψ => ?_⟩
    have hψ : ψ = 0 := by
      apply TestFunction.ext
      intro x
      by_contra hx
      have hxs : x ∈ tsupport (ψ : (Fin 0 → ℝ) → ℝ) := subset_tsupport _ hx
      exact h (hsub x 0 ▸ ψ.tsupport_subset hxs)
    subst hψ
    simp

/-- Apply the hypoellipticity theorem for distributions (real scalar interface) with `c = 0`, `g = 0`
(BB p. 609, proof of Thm 11.62), in positive dimension, for the drift equation with
forcing `0`. -/
theorem exists_smooth_representative_of_hasDistributionEquationWithDrift_of_pos {n q : ℕ}
    (hn : 0 < n) (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (hT : hasDistributionEquationWithDrift Ω X hX T 0) :
    ∃ u : (Fin n → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (Ω : Set (Fin n → ℝ)) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * u x := by
  have hc0 : ContDiffOn ℝ (⊤ : ℕ∞) (0 : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) :=
    contDiffOn_const
  exact Distribution.exists_real_smooth_representative_of_distribution_equation hn Ω X 0 hX
    (lieAlgebraSpansOn_of_bracketSpansOn Ω X hX hspan) hc0 T 0 hc0
    (fun ψ => by rw [adjointTest_zero_eq Ω X hX hc0 ψ]; exact hT.2 ψ)

/-- A smooth representative in pairing form is the distribution of that function. -/
theorem eq_ofFun_of_pairing {n : ℕ} (Ω : Opens (Fin n → ℝ)) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (u : (Fin n → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Ω : Set (Fin n → ℝ)))
    (h : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * u x) :
    T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) := by
  have hui : LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume :=
    hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  ext ψ
  rw [h ψ, Distribution.ofFun_apply hui]
  simp only [smul_eq_mul]

/-- Distributional homogeneous hypoellipticity bridge, with drift (BB p. 609, Thm 11.62):
if `P = ∑ Xᵢ² + X₀` has smooth real Hörmander fields on the open set `Ω` and `T ∈ 𝒟'(Ω)`
satisfies `P T = 0` (`hasDistributionEquationWithDrift Ω X hX T 0`), then `T` is the
distribution of a smooth real function on `Ω`; in particular near each point. -/
theorem exists_smooth_representative_of_hasDistributionEquationWithDrift {n q : ℕ}
    (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (hT : hasDistributionEquationWithDrift Ω X hX T 0) :
    ∃ u : (Fin n → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (Ω : Set (Fin n → ℝ)) ∧
      T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * u x := by
  obtain ⟨u, hu, h⟩ : ∃ u : (Fin n → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (Ω : Set (Fin n → ℝ)) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * u x := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact exists_smooth_representative_of_dim_zero Ω T
    · exact exists_smooth_representative_of_hasDistributionEquationWithDrift_of_pos hn Ω X hX
        hspan T hT
  exact ⟨u, hu, eq_ofFun_of_pairing Ω T u hu h, h⟩

/-- The no-drift form (fields `Fin q`, `P = ∑ Xᵢ²`, `hasDistributionEquation Ω X hX T 0`), through the zero-drift augmentation. -/
theorem exists_smooth_representative_of_hasDistributionEquation {n q : ℕ}
    (Ω : Opens (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (hT : hasDistributionEquation Ω X hX T 0) :
    ∃ u : (Fin n → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (Ω : Set (Fin n → ℝ)) ∧
      T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * u x := by
  refine exists_smooth_representative_of_hasDistributionEquationWithDrift Ω (zeroDrift X)
    (zeroDrift_contDiffOn hX) (bracketSpansOn_zeroDrift hspan) T ⟨hT.1, fun φ => ?_⟩
  rw [sumSquaresWithDriftTransposeTest_zeroDrift]
  exact hT.2 φ

end RothschildStein.P2

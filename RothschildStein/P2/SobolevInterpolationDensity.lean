-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationFarPart
public import RothschildStein.S.CompactSobolevZero
public import RothschildStein.S.SobolevCutoffZero
public import RothschildStein.S.WeakSub
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.Sobolev

/-!
# Sobolev interpolation, compact form: from tests to `W^{2,p}_{X̃,0}` (BB Cor 2.10)

The compact interpolation inequality is first proved for test functions (`CompactInterpolationOn`).
For a function `f` in the closure of the tests in the weighted Sobolev norm
(`memSobolevXZero`, BB Cor 2.10) the inequality passes to the limit, in the form

`∑_l ‖X̃_l f‖_p ≤ ε (∑_l ‖X̃_l² f‖_p + ‖X̃_0 f‖_p) + C ε^{-1} ‖f‖_p`

with the weak norms `weakWordENorm` (`weakWordENorm_interpolation_of_zero`). Here `‖L̃ f‖_p` is
bounded by `∑_l ‖X̃_l² f‖_p + ‖X̃_0 f‖_p` (the words `[l+1, l+1]` and `[0]` have weight two).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}

/-- The compact interpolation inequality for test functions of `V`: for
`0 < ε < εs` and every `v ∈ C_c^∞(V)` on whose support the cutoff `a` is `1`,
`∑_l ‖X̃_l v‖_p ≤ ε ‖L̃ v‖_p + C ε^{-1} ‖v‖_p` (norms in `L^p(V)`). -/
def CompactInterpolationOn (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (V : Opens (Fin n → ℝ))
    (a : TestFunction V ℝ (⊤ : ℕ∞)) (p εs Cp : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < εs → ∀ v : TestFunction V ℝ (⊤ : ℕ∞),
    (∀ x ∈ tsupport (v : (Fin n → ℝ) → ℝ), a x = 1) →
    ∑ l : Fin q, eLpNorm (fieldDerivative (X l.succ) (v : (Fin n → ℝ) → ℝ)) (ENNReal.ofReal p)
        (volume.restrict (V : Set (Fin n → ℝ))) ≤
      ENNReal.ofReal ε * eLpNorm (sumSquaresWithDrift X (v : (Fin n → ℝ) → ℝ)) (ENNReal.ofReal p)
          (volume.restrict (V : Set (Fin n → ℝ))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm (v : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p)
          (volume.restrict (V : Set (Fin n → ℝ)))

section Norms

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {P : ℝ≥0∞}

/-- `‖g‖ ≤ ‖F‖ + ‖g - F‖`. -/
theorem eLpNorm_le_add_sub (hP : 1 ≤ P) (g F : E → ℝ) :
    eLpNorm g P μ ≤ eLpNorm F P μ + eLpNorm (fun x => g x - F x) P μ := by
  have h : g = F + (fun x => g x - F x) := by
    funext x
    simp
  calc eLpNorm g P μ = eLpNorm (F + (fun x => g x - F x)) P μ := by rw [← h]
    _ ≤ _ := eLpNorm_add_le hP

/-- `‖F‖ ≤ ‖g‖ + ‖g - F‖`. -/
theorem eLpNorm_le_add_sub' (hP : 1 ≤ P) (g F : E → ℝ) :
    eLpNorm F P μ ≤ eLpNorm g P μ + eLpNorm (fun x => g x - F x) P μ := by
  have h : F = g + (fun x => F x - g x) := by
    funext x
    simp
  calc eLpNorm F P μ = eLpNorm (g + (fun x => F x - g x)) P μ := by rw [← h]
    _ ≤ eLpNorm g P μ + eLpNorm (fun x => F x - g x) P μ := eLpNorm_add_le hP
    _ = eLpNorm g P μ + eLpNorm (fun x => g x - F x) P μ := by
        congr 1
        exact eLpNorm_sub_comm F g P μ

end Norms

/-- A function continuous on `V` and supported in `Ω' ≤ V` has the same `L^p` norm on `Ω'` and
on `V`. -/
theorem eLpNorm_restrict_eq_of_support {V Ω' : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    {F : (Fin n → ℝ) → ℝ} (hF : ContinuousOn F (V : Set (Fin n → ℝ)))
    (hsupp : Function.support F ⊆ (Ω' : Set (Fin n → ℝ))) (P : ℝ≥0∞) :
    eLpNorm F P (volume.restrict (Ω' : Set (Fin n → ℝ))) =
      eLpNorm F P (volume.restrict (V : Set (Fin n → ℝ))) := by
  have hmeas : AEStronglyMeasurable F (volume.restrict (V : Set (Fin n → ℝ))) :=
    hF.aestronglyMeasurable V.isOpen.measurableSet
  rw [← Measure.restrict_restrict_of_subset (μ := volume) hΩ'V]
  exact eLpNorm_restrict_eq_of_support_subset hmeas hsupp

/-- A test function of `Ω'` extended to a larger open set `V`. -/
def extendTest {V Ω' : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V) (ψ : TestFunction Ω' ℝ (⊤ : ℕ∞)) :
    TestFunction V ℝ (⊤ : ℕ∞) :=
  ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset.trans hΩ'V⟩

theorem extendTest_coe {V Ω' : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    (ψ : TestFunction Ω' ℝ (⊤ : ℕ∞)) :
    (extendTest hΩ'V ψ : (Fin n → ℝ) → ℝ) = ψ := rfl

/-- **One approximation step**: if a smooth `F` with `tsupport F ⊆ Ω' ≤ V` satisfies the compact
inequality (norms over `V`), then for arbitrary `g`-data (the weak derivatives of `f`) the
inequality holds for the `g`'s up to the errors `‖g_I - X̃_I F‖_p`. -/
theorem interpolation_step {V Ω' : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ))) {P : ℝ≥0∞} (hP1 : 1 ≤ P)
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFs : tsupport F ⊆ (Ω' : Set (Fin n → ℝ)))
    {ε Cp : ℝ}
    (hCIF : ∑ l : Fin q, eLpNorm (fieldDerivative (X l.succ) F) P
        (volume.restrict (V : Set (Fin n → ℝ))) ≤
      ENNReal.ofReal ε * eLpNorm (sumSquaresWithDrift X F) P
          (volume.restrict (V : Set (Fin n → ℝ))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm F P (volume.restrict (V : Set (Fin n → ℝ))))
    (g1 g2 : Fin q → (Fin n → ℝ) → ℝ) (g0 gN : (Fin n → ℝ) → ℝ) :
    ∑ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      (ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm g0 P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      ENNReal.ofReal (Cp / ε) * eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      (ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (fun x => g2 l x -
          fieldDerivative (X l.succ) (fieldDerivative (X l.succ) F) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => g0 x - fieldDerivative (X 0) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm (fun x => gN x - F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l.succ) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))) := by
  have hFsm : ContDiffOn ℝ (⊤ : ℕ∞) F (V : Set (Fin n → ℝ)) := hF.contDiffOn
  have hD1 : ∀ l : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (X l.succ) F)
      (V : Set (Fin n → ℝ)) := fun l => S.contDiffOn_fieldDerivative V (X l.succ) F (hXV _) hFsm
  have hD2 : ∀ l : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (X l.succ) (fieldDerivative (X l.succ) F)) (V : Set (Fin n → ℝ)) :=
    fun l => S.contDiffOn_fieldDerivative V (X l.succ) _ (hXV _) (hD1 l)
  have hD0 : ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (X 0) F) (V : Set (Fin n → ℝ)) :=
    S.contDiffOn_fieldDerivative V (X 0) F (hXV _) hFsm
  have hsupp : ∀ I : List (Fin (q + 1)), Function.support (wordDerivative X I F) ⊆
      (Ω' : Set (Fin n → ℝ)) := fun I x hx =>
    hFs (S.tsupport_wordDerivative_subset X I F (subset_tsupport _ hx))
  have hsuppL : Function.support (sumSquaresWithDrift X F) ⊆ (Ω' : Set (Fin n → ℝ)) := by
    intro x hx
    by_contra hxΩ
    apply hx
    exact sumSquaresWithDrift_eq_zero_of_notMem X F (fun h => hxΩ (hFs h))
  have hcontL : ContinuousOn (sumSquaresWithDrift X F) (V : Set (Fin n → ℝ)) := by
    have h : sumSquaresWithDrift X F = fun x => fieldDerivative (X 0) F x +
        ∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) F) x := rfl
    rw [h]
    exact hD0.continuousOn.add (continuousOn_finsetSum _ fun i _ => (hD2 i).continuousOn)
  have hnorm : ∀ G : (Fin n → ℝ) → ℝ, ContinuousOn G (V : Set (Fin n → ℝ)) →
      Function.support G ⊆ (Ω' : Set (Fin n → ℝ)) →
      eLpNorm G P (volume.restrict (V : Set (Fin n → ℝ))) =
        eLpNorm G P (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun G hG hs =>
    (eLpNorm_restrict_eq_of_support hΩ'V hG hs P).symm
  have hsumeq : ∑ l : Fin q, eLpNorm (fieldDerivative (X l.succ) F) P
      (volume.restrict (V : Set (Fin n → ℝ))) =
      ∑ l : Fin q, eLpNorm (fieldDerivative (X l.succ) F) P
        (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    Finset.sum_congr rfl fun l _ => hnorm _ (hD1 l).continuousOn (hsupp [l.succ])
  rw [hsumeq, hnorm _ hcontL hsuppL, hnorm F hFsm.continuousOn
    (fun x hx => hFs (subset_tsupport _ hx))] at hCIF
  -- the triangle inequalities
  have hA : ∀ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm (fieldDerivative (X l.succ) F) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => g1 l x - fieldDerivative (X l.succ) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l => eLpNorm_le_add_sub hP1 (g1 l) _
  have hLj : eLpNorm (sumSquaresWithDrift X F) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      (eLpNorm (fieldDerivative (X 0) F) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fieldDerivative (X l.succ) (fieldDerivative (X l.succ) F)) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))) := by
    have h : sumSquaresWithDrift X F = fieldDerivative (X 0) F +
        ∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) F) := by
      funext x
      simp [sumSquaresWithDrift, Finset.sum_apply]
    rw [h]
    exact (eLpNorm_add_le hP1).trans (add_le_add le_rfl (eLpNorm_sum_le hP1))
  have h0 : eLpNorm (fieldDerivative (X 0) F) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm g0 P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => g0 x - fieldDerivative (X 0) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := eLpNorm_le_add_sub' hP1 g0 _
  have h2 : ∀ l : Fin q, eLpNorm (fieldDerivative (X l.succ) (fieldDerivative (X l.succ) F)) P
      (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => g2 l x - fieldDerivative (X l.succ) (fieldDerivative (X l.succ) F) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l => eLpNorm_le_add_sub' hP1 (g2 l) _
  have hN : eLpNorm F P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => gN x - F x) P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    eLpNorm_le_add_sub' hP1 gN _
  calc ∑ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ)))
      ≤ ∑ l : Fin q, (eLpNorm (fieldDerivative (X l.succ) F) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => g1 l x - fieldDerivative (X l.succ) F x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ)))) := Finset.sum_le_sum fun l _ => hA l
    _ = ∑ l : Fin q, eLpNorm (fieldDerivative (X l.succ) F) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l.succ) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := Finset.sum_add_distrib
    _ ≤ (ENNReal.ofReal ε * eLpNorm (sumSquaresWithDrift X F) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm F P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l.succ) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := add_le_add hCIF le_rfl
    _ ≤ (ENNReal.ofReal ε * ((eLpNorm g0 P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
            eLpNorm (fun x => g0 x - fieldDerivative (X 0) F x) P
              (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
          ∑ l : Fin q, (eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
            eLpNorm (fun x => g2 l x - fieldDerivative (X l.succ)
              (fieldDerivative (X l.succ) F) x) P (volume.restrict (Ω' : Set (Fin n → ℝ))))) +
        ENNReal.ofReal (Cp / ε) * (eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => gN x - F x) P (volume.restrict (Ω' : Set (Fin n → ℝ))))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l.succ) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl (hLj.trans (add_le_add h0
          (Finset.sum_le_sum fun l _ => h2 l)))) (mul_le_mul' le_rfl hN)) le_rfl
    _ = _ := by
        rw [Finset.sum_add_distrib]
        ring

/-- **The compact interpolation inequality for `W^{2,p}_{X̃,0}`** (BB Cor 2.10): if `Ω' ≤ V` and `a = 1`
on `Ω'`, and `f ∈ W^{2,p}_{X̃,0}(Ω')`, then for `0 < ε < εs`
`∑_l ‖X̃_l f‖_p ≤ ε (∑_l ‖X̃_l² f‖_p + ‖X̃_0 f‖_p) + C ε^{-1} ‖f‖_p`
(weak norms on `Ω'`). -/
theorem weakWordENorm_interpolation_of_zero
    (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p εs Cp : ℝ} (hp : 1 < p)
    (hCI : CompactInterpolationOn X V a p εs Cp) {Ω' : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    (hΩ'a : ∀ x ∈ (Ω' : Set (Fin n → ℝ)), a x = 1) {f : (Fin n → ℝ) → ℝ}
    (hf : memSobolevXZero w X Ω' 2 (ENNReal.ofReal p) f) {ε : ℝ} (hε : 0 < ε) (hεs : ε < εs) :
    ∑ l : Fin q, weakWordENorm X Ω' [l.succ] (ENNReal.ofReal p) f ≤
      ENNReal.ofReal ε * (∑ l : Fin q, weakWordENorm X Ω' [l.succ, l.succ] (ENNReal.ofReal p) f +
        weakWordENorm X Ω' [0] (ENNReal.ofReal p) f) +
      ENNReal.ofReal (Cp / ε) * weakWordENorm X Ω' [] (ENNReal.ofReal p) f := by
  obtain ⟨hfS, ψ, hψ⟩ := hf
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hXΩ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω' : Set (Fin n → ℝ)) := fun i =>
    (hXV i).mono hΩ'V
  -- words of weight at most two
  have hmem1 : ∀ l : Fin q, [l.succ] ∈ wordFamily w 2 := fun l => by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw l]
  have hmem2 : ∀ l : Fin q, [l.succ, l.succ] ∈ wordFamily w 2 := fun l => by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw l]
  have hmem0 : [(0 : Fin (q + 1))] ∈ wordFamily w 2 := by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw0]
  have hmemN : ([] : List (Fin (q + 1))) ∈ wordFamily w 2 := S.nil_mem_wordFamily w 2
  choose g1 hg1 using fun l : Fin q => hfS.2 [l.succ] (hmem1 l)
  choose g2 hg2 using fun l : Fin q => hfS.2 [l.succ, l.succ] (hmem2 l)
  obtain ⟨g0, hg0, -⟩ := hfS.2 [0] hmem0
  obtain ⟨gN, hgN, -⟩ := hfS.2 [] hmemN
  -- the weak norms are the norms of the representatives
  have e1 : ∀ l : Fin q, weakWordENorm X Ω' [l.succ] P f =
      eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ω' _ P f _ (hg1 l).1
  have e2 : ∀ l : Fin q, weakWordENorm X Ω' [l.succ, l.succ] P f =
      eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ω' _ P f _ (hg2 l).1
  have e0 : weakWordENorm X Ω' [0] P f = eLpNorm g0 P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ω' _ P f _ hg0
  have eN : weakWordENorm X Ω' [] P f = eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ω' _ P f _ hgN
  simp only [e1, e2, e0, eN]
  -- convergence of the errors
  have hconv : ∀ (I : List (Fin (q + 1))), I ∈ wordFamily w 2 → ∀ g : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X Ω' I f g →
      Tendsto (fun j => eLpNorm (fun x => g x - wordDerivative X I (ψ j) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) := by
    intro I hI g hg
    have hle : ∀ j, eLpNorm (fun x => g x - wordDerivative X I (ψ j) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
        sobolevXENorm w X Ω' 2 P (fun x => f x - ψ j x) := by
      intro j
      have hs := S.hasWeakWordDeriv_sub X Ω' hXΩ hg
        (S.hasWeakWordDeriv_classical Ω' X hXΩ I (ψ j) (ψ j).contDiff.contDiffOn)
      rw [← S.weakWordENorm_eq X Ω' I P _ _ hs]
      exact Finset.single_le_sum (f := fun I => weakWordENorm X Ω' I P (fun x => f x - ψ j x))
        (fun _ _ => zero_le) hI
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hψ (fun _ => zero_le) hle
  have c1 : ∀ l : Fin q, Tendsto (fun j => eLpNorm (fun x => g1 l x -
      fieldDerivative (X l.succ) (ψ j : (Fin n → ℝ) → ℝ) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) := fun l =>
    hconv [l.succ] (hmem1 l) (g1 l) (hg1 l).1
  have c2 : ∀ l : Fin q, Tendsto (fun j => eLpNorm (fun x => g2 l x -
      fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (ψ j : (Fin n → ℝ) → ℝ)) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) := fun l =>
    hconv [l.succ, l.succ] (hmem2 l) (g2 l) (hg2 l).1
  have c0 : Tendsto (fun j => eLpNorm (fun x => g0 x -
      fieldDerivative (X 0) (ψ j : (Fin n → ℝ) → ℝ) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) :=
    hconv [0] hmem0 g0 hg0
  have cN : Tendsto (fun j => eLpNorm (fun x => gN x - (ψ j : (Fin n → ℝ) → ℝ) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) :=
    hconv [] hmemN gN hgN
  have hE : Tendsto (fun j => ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (fun x => g2 l x -
          fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (ψ j : (Fin n → ℝ) → ℝ)) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => g0 x - fieldDerivative (X 0) (ψ j : (Fin n → ℝ) → ℝ) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm (fun x => gN x - (ψ j : (Fin n → ℝ) → ℝ) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l.succ)
          (ψ j : (Fin n → ℝ) → ℝ) x) P (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) := by
    have t1 := tendsto_finsetSum (Finset.univ : Finset (Fin q)) (fun l _ => c1 l)
    have t2 := tendsto_finsetSum (Finset.univ : Finset (Fin q)) (fun l _ => c2 l)
    have t3 := t2.add c0
    have t4 := ENNReal.Tendsto.const_mul t3 (Or.inr (ENNReal.ofReal_ne_top (r := ε)))
    have t5 := ENNReal.Tendsto.const_mul cN (Or.inr (ENNReal.ofReal_ne_top (r := Cp / ε)))
    have := (t4.add t5).add t1
    simpa using this
  -- the estimate for each approximant
  have hmain : ∀ j, ∑ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      (ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (g2 l) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm g0 P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      ENNReal.ofReal (Cp / ε) * eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      (ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (fun x => g2 l x -
          fieldDerivative (X l.succ) (fieldDerivative (X l.succ) (ψ j : (Fin n → ℝ) → ℝ)) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => g0 x - fieldDerivative (X 0) (ψ j : (Fin n → ℝ) → ℝ) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm (fun x => gN x - (ψ j : (Fin n → ℝ) → ℝ) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l.succ)
          (ψ j : (Fin n → ℝ) → ℝ) x) P (volume.restrict (Ω' : Set (Fin n → ℝ)))) := by
    intro j
    have hCIj := hCI ε hε hεs (extendTest hΩ'V (ψ j)) (fun x hx => hΩ'a x ((ψ j).tsupport_subset hx))
    simp only [extendTest_coe] at hCIj
    exact interpolation_step hΩ'V hXV hP1 (ψ j).contDiff (ψ j).tsupport_subset hCIj g1 g2 g0 gN
  have hlim := (tendsto_const_nhds (x := ENNReal.ofReal ε * (∑ l : Fin q,
      eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
      eLpNorm g0 P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      ENNReal.ofReal (Cp / ε) * eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ))))).add hE
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hmain

end RothschildStein.P2

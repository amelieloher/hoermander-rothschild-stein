-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationDensity
public import RothschildStein.P2.SobolevInterpolationNoDriftFarPart

/-!
# Sobolev interpolation without drift, seminorm absorption: the compact interpolation inequality for `W^{2,p}_{X̃,0}`

The no-drift counterpart of `SobolevInterpolationDensity` (alphabet `Fin q`, all weights one,
`L̃ = sumSquares`). `CompactInterpolationOnNoDrift` is the compact inequality for test functions
(`exists_compactInterpolation_noDrift_of_representation`); by S's density (`memSobolevXZero`) it extends
to `W^{2,p}_{X̃,0}(Ω')`, with the weak derivatives in place of the classical ones
(`weakWordENorm_interpolation_of_zero_noDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein

variable {n q : ℕ} {w : Fin q → ℕ+} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}

/-- The compact interpolation inequality for test functions of `V`, no
drift: for `0 < ε < εs` and every `v ∈ C_c^∞(V)` on whose support the cutoff `a` is `1`,
`∑_l ‖X̃_l v‖_p ≤ ε ‖L̃ v‖_p + C ε^{-1} ‖v‖_p` (norms in `L^p(V)`, `L̃ = sumSquares`). -/
def CompactInterpolationOnNoDrift (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (V : Opens (Fin n → ℝ))
    (a : TestFunction V ℝ (⊤ : ℕ∞)) (p εs Cp : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < εs → ∀ v : TestFunction V ℝ (⊤ : ℕ∞),
    (∀ x ∈ tsupport (v : (Fin n → ℝ) → ℝ), a x = 1) →
    ∑ l : Fin q, eLpNorm (fieldDerivative (X l) (v : (Fin n → ℝ) → ℝ)) (ENNReal.ofReal p)
        (volume.restrict (V : Set (Fin n → ℝ))) ≤
      ENNReal.ofReal ε * eLpNorm (sumSquares X (v : (Fin n → ℝ) → ℝ)) (ENNReal.ofReal p)
          (volume.restrict (V : Set (Fin n → ℝ))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm (v : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p)
          (volume.restrict (V : Set (Fin n → ℝ)))

/-- **One approximation step, no drift**: if a smooth `F` with `tsupport F ⊆ Ω' ≤ V` satisfies
the compact inequality (norms over `V`), then for arbitrary `g`-data (the weak derivatives of `f`) the
inequality holds for the `g`'s up to the errors `‖g_I - X̃_I F‖_p`. -/
theorem interpolation_step_noDrift {V Ω' : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ))) {P : ℝ≥0∞} (hP1 : 1 ≤ P)
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFs : tsupport F ⊆ (Ω' : Set (Fin n → ℝ)))
    {ε Cp : ℝ}
    (hCIF : ∑ l : Fin q, eLpNorm (fieldDerivative (X l) F) P
        (volume.restrict (V : Set (Fin n → ℝ))) ≤
      ENNReal.ofReal ε * eLpNorm (sumSquares X F) P (volume.restrict (V : Set (Fin n → ℝ))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm F P (volume.restrict (V : Set (Fin n → ℝ))))
    (g1 g2 : Fin q → (Fin n → ℝ) → ℝ) (gN : (Fin n → ℝ) → ℝ) :
    ∑ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      (ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      ENNReal.ofReal (Cp / ε) * eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      (ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (fun x => g2 l x -
          fieldDerivative (X l) (fieldDerivative (X l) F) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm (fun x => gN x - F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))) := by
  have hFsm : ContDiffOn ℝ (⊤ : ℕ∞) F (V : Set (Fin n → ℝ)) := hF.contDiffOn
  have hD1 : ∀ l : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (X l) F)
      (V : Set (Fin n → ℝ)) := fun l => S.contDiffOn_fieldDerivative V (X l) F (hXV _) hFsm
  have hD2 : ∀ l : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (X l) (fieldDerivative (X l) F)) (V : Set (Fin n → ℝ)) :=
    fun l => S.contDiffOn_fieldDerivative V (X l) _ (hXV _) (hD1 l)
  have hsupp : ∀ I : List (Fin q), Function.support (wordDerivative X I F) ⊆
      (Ω' : Set (Fin n → ℝ)) := fun I x hx =>
    hFs (S.tsupport_wordDerivative_subset X I F (subset_tsupport _ hx))
  have hsuppL : Function.support (sumSquares X F) ⊆ (Ω' : Set (Fin n → ℝ)) := by
    intro x hx
    by_contra hxΩ
    apply hx
    exact sumSquares_eq_zero_of_notMem_noDrift X F (fun h => hxΩ (hFs h))
  have hcontL : ContinuousOn (sumSquares X F) (V : Set (Fin n → ℝ)) := by
    have h : sumSquares X F = fun x =>
        ∑ i : Fin q, fieldDerivative (X i) (fieldDerivative (X i) F) x := rfl
    rw [h]
    exact continuousOn_finsetSum _ fun i _ => (hD2 i).continuousOn
  have hnorm : ∀ G : (Fin n → ℝ) → ℝ, ContinuousOn G (V : Set (Fin n → ℝ)) →
      Function.support G ⊆ (Ω' : Set (Fin n → ℝ)) →
      eLpNorm G P (volume.restrict (V : Set (Fin n → ℝ))) =
        eLpNorm G P (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun G hG hs =>
    (eLpNorm_restrict_eq_of_support hΩ'V hG hs P).symm
  have hsumeq : ∑ l : Fin q, eLpNorm (fieldDerivative (X l) F) P
      (volume.restrict (V : Set (Fin n → ℝ))) =
      ∑ l : Fin q, eLpNorm (fieldDerivative (X l) F) P
        (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    Finset.sum_congr rfl fun l _ => hnorm _ (hD1 l).continuousOn (hsupp [l])
  rw [hsumeq, hnorm _ hcontL hsuppL, hnorm F hFsm.continuousOn
    (fun x hx => hFs (subset_tsupport _ hx))] at hCIF
  -- the triangle inequalities
  have hA : ∀ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm (fieldDerivative (X l) F) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => g1 l x - fieldDerivative (X l) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l => eLpNorm_le_add_sub hP1 (g1 l) _
  have hLj : eLpNorm (sumSquares X F) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      ∑ l : Fin q, eLpNorm (fieldDerivative (X l) (fieldDerivative (X l) F)) P
        (volume.restrict (Ω' : Set (Fin n → ℝ))) := by
    have h : sumSquares X F =
        ∑ i : Fin q, fieldDerivative (X i) (fieldDerivative (X i) F) := by
      funext x
      simp [sumSquares, Finset.sum_apply]
    rw [h]
    exact eLpNorm_sum_le hP1
  have h2 : ∀ l : Fin q, eLpNorm (fieldDerivative (X l) (fieldDerivative (X l) F)) P
      (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => g2 l x - fieldDerivative (X l) (fieldDerivative (X l) F) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l => eLpNorm_le_add_sub' hP1 (g2 l) _
  have hN : eLpNorm F P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm (fun x => gN x - F x) P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    eLpNorm_le_add_sub' hP1 gN _
  calc ∑ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ)))
      ≤ ∑ l : Fin q, (eLpNorm (fieldDerivative (X l) F) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => g1 l x - fieldDerivative (X l) F x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ)))) := Finset.sum_le_sum fun l _ => hA l
    _ = ∑ l : Fin q, eLpNorm (fieldDerivative (X l) F) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := Finset.sum_add_distrib
    _ ≤ (ENNReal.ofReal ε * eLpNorm (sumSquares X F) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm F P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) := add_le_add hCIF le_rfl
    _ ≤ (ENNReal.ofReal ε * (∑ l : Fin q, (eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
            eLpNorm (fun x => g2 l x - fieldDerivative (X l)
              (fieldDerivative (X l) F) x) P (volume.restrict (Ω' : Set (Fin n → ℝ))))) +
        ENNReal.ofReal (Cp / ε) * (eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => gN x - F x) P (volume.restrict (Ω' : Set (Fin n → ℝ))))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l) F x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl (hLj.trans
          (Finset.sum_le_sum fun l _ => h2 l))) (mul_le_mul' le_rfl hN)) le_rfl
    _ = _ := by
        rw [Finset.sum_add_distrib]
        ring

/-- **The compact interpolation inequality for `W^{2,p}_{X̃,0}`, no drift** (BB Cor 2.10): if `Ω' ≤ V`
and `a = 1` on `Ω'`, and `f ∈ W^{2,p}_{X̃,0}(Ω')`, then for `0 < ε < εs`
`∑_l ‖X̃_l f‖_p ≤ ε ∑_l ‖X̃_l² f‖_p + C ε^{-1} ‖f‖_p` (weak norms on `Ω'`). -/
theorem weakWordENorm_interpolation_of_zero_noDrift
    (hw : ∀ j, (w j : ℕ) = 1) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p εs Cp : ℝ} (hp : 1 < p)
    (hCI : CompactInterpolationOnNoDrift X V a p εs Cp) {Ω' : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    (hΩ'a : ∀ x ∈ (Ω' : Set (Fin n → ℝ)), a x = 1) {f : (Fin n → ℝ) → ℝ}
    (hf : memSobolevXZero w X Ω' 2 (ENNReal.ofReal p) f) {ε : ℝ} (hε : 0 < ε) (hεs : ε < εs) :
    ∑ l : Fin q, weakWordENorm X Ω' [l] (ENNReal.ofReal p) f ≤
      ENNReal.ofReal ε * (∑ l : Fin q, weakWordENorm X Ω' [l, l] (ENNReal.ofReal p) f) +
      ENNReal.ofReal (Cp / ε) * weakWordENorm X Ω' [] (ENNReal.ofReal p) f := by
  obtain ⟨hfS, ψ, hψ⟩ := hf
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hXΩ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω' : Set (Fin n → ℝ)) := fun i =>
    (hXV i).mono hΩ'V
  -- words of weight at most two
  have hmem1 : ∀ l : Fin q, [l] ∈ wordFamily w 2 := fun l => by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw l]
  have hmem2 : ∀ l : Fin q, [l, l] ∈ wordFamily w 2 := fun l => by
    rw [S.mem_wordFamily_iff]
    simp [wordWeight, hw l]
  have hmemN : ([] : List (Fin q)) ∈ wordFamily w 2 := S.nil_mem_wordFamily w 2
  choose g1 hg1 using fun l : Fin q => hfS.2 [l] (hmem1 l)
  choose g2 hg2 using fun l : Fin q => hfS.2 [l, l] (hmem2 l)
  obtain ⟨gN, hgN, -⟩ := hfS.2 [] hmemN
  -- the weak norms are the norms of the representatives
  have e1 : ∀ l : Fin q, weakWordENorm X Ω' [l] P f =
      eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ω' _ P f _ (hg1 l).1
  have e2 : ∀ l : Fin q, weakWordENorm X Ω' [l, l] P f =
      eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) := fun l =>
    S.weakWordENorm_eq X Ω' _ P f _ (hg2 l).1
  have eN : weakWordENorm X Ω' [] P f = eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ω' _ P f _ hgN
  simp only [e1, e2, eN]
  -- convergence of the errors
  have hconv : ∀ (I : List (Fin q)), I ∈ wordFamily w 2 → ∀ g : (Fin n → ℝ) → ℝ,
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
      fieldDerivative (X l) (ψ j : (Fin n → ℝ) → ℝ) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) := fun l =>
    hconv [l] (hmem1 l) (g1 l) (hg1 l).1
  have c2 : ∀ l : Fin q, Tendsto (fun j => eLpNorm (fun x => g2 l x -
      fieldDerivative (X l) (fieldDerivative (X l) (ψ j : (Fin n → ℝ) → ℝ)) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) := fun l =>
    hconv [l, l] (hmem2 l) (g2 l) (hg2 l).1
  have cN : Tendsto (fun j => eLpNorm (fun x => gN x - (ψ j : (Fin n → ℝ) → ℝ) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) :=
    hconv [] hmemN gN hgN
  have hE : Tendsto (fun j => ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (fun x => g2 l x -
          fieldDerivative (X l) (fieldDerivative (X l) (ψ j : (Fin n → ℝ) → ℝ)) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm (fun x => gN x - (ψ j : (Fin n → ℝ) → ℝ) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l)
          (ψ j : (Fin n → ℝ) → ℝ) x) P (volume.restrict (Ω' : Set (Fin n → ℝ)))) atTop (𝓝 0) := by
    have t1 := tendsto_finsetSum (Finset.univ : Finset (Fin q)) (fun l _ => c1 l)
    have t2 := tendsto_finsetSum (Finset.univ : Finset (Fin q)) (fun l _ => c2 l)
    have t4 := ENNReal.Tendsto.const_mul t2 (Or.inr (ENNReal.ofReal_ne_top (r := ε)))
    have t5 := ENNReal.Tendsto.const_mul cN (Or.inr (ENNReal.ofReal_ne_top (r := Cp / ε)))
    have := (t4.add t5).add t1
    simpa using this
  -- the estimate for each approximant
  have hmain : ∀ j, ∑ l : Fin q, eLpNorm (g1 l) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      (ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (g2 l) P
          (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      ENNReal.ofReal (Cp / ε) * eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      (ENNReal.ofReal ε * (∑ l : Fin q, eLpNorm (fun x => g2 l x -
          fieldDerivative (X l) (fieldDerivative (X l) (ψ j : (Fin n → ℝ) → ℝ)) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
        ENNReal.ofReal (Cp / ε) * eLpNorm (fun x => gN x - (ψ j : (Fin n → ℝ) → ℝ) x) P
          (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        ∑ l : Fin q, eLpNorm (fun x => g1 l x - fieldDerivative (X l)
          (ψ j : (Fin n → ℝ) → ℝ) x) P (volume.restrict (Ω' : Set (Fin n → ℝ)))) := by
    intro j
    have hCIj := hCI ε hε hεs (extendTest hΩ'V (ψ j)) (fun x hx => hΩ'a x ((ψ j).tsupport_subset hx))
    simp only [extendTest_coe] at hCIj
    exact interpolation_step_noDrift hΩ'V hXV hP1 (ψ j).contDiff (ψ j).tsupport_subset hCIj g1 g2 gN
  have hlim := (tendsto_const_nhds (x := ENNReal.ofReal ε * (∑ l : Fin q,
      eLpNorm (g2 l) P (volume.restrict (Ω' : Set (Fin n → ℝ)))) +
      ENNReal.ofReal (Cp / ε) * eLpNorm gN P (volume.restrict (Ω' : Set (Fin n → ℝ))))).add hE
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hmain

end RothschildStein.P2

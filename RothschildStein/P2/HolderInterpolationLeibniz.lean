-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.ProductAbsorptionWeak
public import RothschildStein.P1.WeakExtensionHolder
public import RothschildStein.P1.ParametrixKernelBoundsRight
public import RothschildStein.P1.ContinuityTheoremHolder
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.driftWeight

/-!
# Nested Hölder interpolation: Leibniz jets of a cutoff product

For a smooth compactly supported multiplier `ζ` (a radial cutoff) with `tsupport ζ ⊆ V` and a function `u`
with a Hölder weak jet `D` on the patch `V`, the product `u ζ` has the Hölder weak jet `prodJet`
(the Leibniz rule for the words of weight at most two: `[]`, `[i]`, `[j, i]`), supported in
`tsupport ζ`; products of a smooth compactly supported multiplier with a function of finite Hölder norm
have finite Hölder norm (Leibniz rule in `C^{k,α}_{X̃}`, continuity theorem). In particular `L̃ (u ζ) = ζ L̃u + 2 ∑ᵢ X̃ᵢζ X̃ᵢu + u L̃ζ`
(`weakSumSquaresWithDrift_prodJet`). This is the localization step of the nested Hölder interpolation inequality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Words

variable {q : ℕ}

/-- The words of weight at most two over the drift alphabet: the empty
word, one letter, or two horizontal letters. -/
theorem wordFamily_drift_cases {K : List (Fin (q + 1))} (hK : K ∈ wordFamily driftWeight 2) :
    K = [] ∨ (∃ i, K = [i]) ∨ ∃ j i : Fin q, K = [j.succ, i.succ] := by
  rw [S.mem_wordFamily_iff] at hK
  rcases K with _ | ⟨a, _ | ⟨b, _ | ⟨c, K⟩⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨a, rfl⟩)
  · right; right
    have ha : a ≠ 0 := by
      intro h
      subst h
      by_cases hb : b = 0 <;> simp [wordWeight, driftWeight, hb] at hK
    have hb : b ≠ 0 := by
      intro h
      subst h
      by_cases ha' : a = 0 <;> simp [wordWeight, driftWeight, ha'] at hK
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 ha
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hb
    exact ⟨j, i, rfl⟩
  · exfalso
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
      simp [wordWeight, driftWeight, ha, hb, hc] at hK <;> omega

end Words

variable {q N : ℕ}

/-- The Leibniz jet of a product `u ζ` for the words of weight at most
two (all other words are given the value `0`). -/
def prodJet (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (ζ u : (Fin N → ℝ) → ℝ)
    (D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ
  | [] => fun x => u x * ζ x
  | [i] => fun x => D [i] x * ζ x + u x * fieldDerivative (X i) ζ x
  | [j, i] => fun x => (D [j, i] x * ζ x + D [i] x * fieldDerivative (X j) ζ x) +
      (D [j] x * fieldDerivative (X i) ζ x + u x * fieldDerivative (X j) (fieldDerivative (X i) ζ) x)
  | _ => fun _ => 0

/-- The weak first-order Leibniz rule for the jet of `u ζ`. -/
theorem hasWeakWordDeriv_prodJet_single {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    {V : Opens (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin N → ℝ)))
    {ζ u : (Fin N → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ}
    (hζ : ContDiffOn ℝ (⊤ : ℕ∞) ζ (V : Set (Fin N → ℝ))) (i : Fin (q + 1))
    (hi : hasWeakWordDeriv X V [i] u (D [i])) :
    hasWeakWordDeriv X V [i] (fun x => u x * ζ x) (prodJet X ζ u D [i]) :=
  S.hasWeakWordDeriv_mul_one X V hX i u (D [i]) ζ hζ hi

/-- The weak second-order Leibniz rule for the jet of `u ζ`. -/
theorem hasWeakWordDeriv_prodJet_pair {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    {V : Opens (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin N → ℝ)))
    {ζ u : (Fin N → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ}
    (hζ : ContDiffOn ℝ (⊤ : ℕ∞) ζ (V : Set (Fin N → ℝ))) (j i : Fin (q + 1))
    (hi : hasWeakWordDeriv X V [i] u (D [i])) (hj : hasWeakWordDeriv X V [j] u (D [j]))
    (hji : hasWeakWordDeriv X V [j, i] u (D [j, i])) :
    hasWeakWordDeriv X V [j, i] (fun x => u x * ζ x) (prodJet X ζ u D [j, i]) := by
  have h1 := S.hasWeakWordDeriv_mul_one X V hX i u (D [i]) ζ hζ hi
  have hji' : hasWeakWordDeriv X V [j] (D [i]) (D [j, i]) :=
    (S.hasWeakWordDeriv_cons_iff X V hX hi j).mp hji
  have h2a := S.hasWeakWordDeriv_mul_one X V hX j (D [i]) (D [j, i]) ζ hζ hji'
  have hXi : ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (X i) ζ) (V : Set (Fin N → ℝ)) :=
    S.contDiffOn_fieldDerivative V (X i) ζ (hX i) hζ
  have h2b := S.hasWeakWordDeriv_mul_one X V hX j u (D [j]) (fieldDerivative (X i) ζ) hXi hj
  have h2 := S.hasWeakWordDeriv_add X V hX h2a h2b
  exact (S.hasWeakWordDeriv_cons_iff X V hX h1 j).mpr h2

variable {n st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart driftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **Products with a smooth compactly supported multiplier keep finite
Hölder norm** (the continuity theorem and the Leibniz rule in `C^{k,α}_{X̃}`). -/
theorem holderENorm_mul_ne_top (hF : C.IsLiftedFrame F) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {b : (Fin (n + m) → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b)
    (hbV : tsupport b ⊆ (F.V : Set (Fin (n + m) → ℝ))) {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤) :
    holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => f x * b x) ≠ ⊤ := by
  obtain ⟨K, -, hK⟩ := LiftedChart.exists_holderENorm_mul_le (C := C) F.V.isOpen hF.subset_U hb hbc
    hbV hα0 hα1
  have e : (fun x => f x * b x) = fun x => b x * f x := funext fun x => mul_comm _ _
  rw [e]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf) (hK f)

/-- The derivatives `X̃ᵢ ζ`, `X̃ⱼ X̃ᵢ ζ` of a smooth cutoff supported in
the patch are smooth with compact support in the patch. -/
theorem cutoff_derivative_data (hF : C.IsLiftedFrame F) {ζ : (Fin (n + m) → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (hζV : tsupport ζ ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) ζ)) ∧
    (∀ i, HasCompactSupport (fieldDerivative (C.Xl i) ζ)) ∧
    (∀ i, tsupport (fieldDerivative (C.Xl i) ζ) ⊆ (F.V : Set (Fin (n + m) → ℝ))) ∧
    (∀ j i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) ζ))) ∧
    (∀ j i, HasCompactSupport (fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) ζ))) ∧
    (∀ j i, tsupport (fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) ζ)) ⊆
      (F.V : Set (Fin (n + m) → ℝ))) := by
  have hU : tsupport ζ ⊆ C.U := hζV.trans hF.subset_U
  have h1 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) ζ) := fun i =>
    LiftedChart.contDiff_fieldDerivative_Xl hζ hU i
  have s1 : ∀ i, tsupport (fieldDerivative (C.Xl i) ζ) ⊆ tsupport ζ := fun i =>
    tsupport_fieldDerivative_subset _ _
  have s2 : ∀ j i, tsupport (fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) ζ)) ⊆ tsupport ζ :=
    fun j i => (tsupport_fieldDerivative_subset _ _).trans (s1 i)
  refine ⟨h1, fun i => hζc.of_isClosed_subset (isClosed_tsupport _) (s1 i),
    fun i => (s1 i).trans hζV, fun j i => ?_, fun j i => ?_, fun j i => (s2 j i).trans hζV⟩
  · exact LiftedChart.contDiff_fieldDerivative_Xl (h1 i) ((s1 i).trans hU) j
  · exact hζc.of_isClosed_subset (isClosed_tsupport _) (s2 j i)

/-- **The Leibniz jet is a Hölder weak jet**: if `u` has finite Hölder norm
and the Hölder weak jet `D` on the patch, and `ζ` is a smooth cutoff with `tsupport ζ ⊆ V` compact,
then `prodJet C.Xl ζ u D` is a Hölder weak jet of `u ζ`. -/
theorem isHolderWeakJet_prodJet (hF : C.IsLiftedFrame F) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {ζ u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (hζV : tsupport ζ ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (hu : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤)
    (hD : LiftedChart.IsHolderWeakJet driftWeight C.Xl C.dl F.V 2 α u D) :
    LiftedChart.IsHolderWeakJet driftWeight C.Xl C.dl F.V 2 α (fun x => u x * ζ x)
      (prodJet C.Xl ζ u D) := by
  obtain ⟨c1, cc1, cV1, c2, cc2, cV2⟩ := cutoff_derivative_data hF hζ hζc hζV
  have hXV := hF.contDiffOn_Xl
  have hζ' : ContDiffOn ℝ (⊤ : ℕ∞) ζ (F.V : Set (Fin (n + m) → ℝ)) := hζ.contDiffOn
  have hmul := fun {b : (Fin (n + m) → ℝ) → ℝ} {f : (Fin (n + m) → ℝ) → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b)
    (hbV : tsupport b ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤) =>
    holderENorm_mul_ne_top hF hα0 hα1 hb hbc hbV hf
  have hadd : ∀ f g : (Fin (n + m) → ℝ) → ℝ,
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤ →
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤ →
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => f x + g x) ≠ ⊤ :=
    fun f g hf hg => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, hg⟩)
      (holderENorm_add_le hα0.le _ _)
  have hum : ContinuousOn u (F.V : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0 (lt_top_iff_ne_top.2 hu)
  intro K hK
  have hDK : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl F.V I u (D I) ∧
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D I) ≠ ⊤ := hD
  rcases wordFamily_drift_cases hK with rfl | ⟨i, rfl⟩ | ⟨j, i, rfl⟩
  · refine ⟨?_, hmul hζ hζc hζV hu⟩
    exact S.hasWeakWordDeriv_nil C.Xl F.V
      ((hum.mul hζ.continuous.continuousOn).locallyIntegrableOn F.V.isOpen.measurableSet)
  · have hmem : [i] ∈ wordFamily driftWeight 2 := hK
    obtain ⟨hw1, hh1⟩ := hDK [i] hmem
    exact ⟨hasWeakWordDeriv_prodJet_single hXV hζ' i hw1,
      hadd _ _ (hmul hζ hζc hζV hh1) (hmul (c1 i) (cc1 i) (cV1 i) hu)⟩
  · have hmem : [j.succ, i.succ] ∈ wordFamily driftWeight 2 := hK
    have hmi : [i.succ] ∈ wordFamily driftWeight 2 := (S.mem_wordFamily_iff _ _ _).2 (by
      simp [wordWeight, driftWeight, Fin.succ_ne_zero])
    have hmj : [j.succ] ∈ wordFamily driftWeight 2 := (S.mem_wordFamily_iff _ _ _).2 (by
      simp [wordWeight, driftWeight, Fin.succ_ne_zero])
    obtain ⟨hwi, hhi⟩ := hDK [i.succ] hmi
    obtain ⟨hwj, hhj⟩ := hDK [j.succ] hmj
    obtain ⟨hwji, hhji⟩ := hDK [j.succ, i.succ] hmem
    refine ⟨hasWeakWordDeriv_prodJet_pair hXV hζ' j.succ i.succ hwi hwj hwji, ?_⟩
    exact hadd _ _ (hadd _ _ (hmul hζ hζc hζV hhji) (hmul (c1 j.succ) (cc1 j.succ) (cV1 j.succ) hhi))
      (hadd _ _ (hmul (c1 i.succ) (cc1 i.succ) (cV1 i.succ) hhj)
        (hmul (c2 j.succ i.succ) (cc2 j.succ i.succ) (cV2 j.succ i.succ) hu))

/-- **`L̃ (u ζ) = ζ L̃u + 2 ∑ᵢ X̃ᵢζ X̃ᵢu + u L̃ζ`** for the Leibniz jet. -/
theorem weakSumSquaresWithDrift_prodJet (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (ζ u : (Fin N → ℝ) → ℝ) (D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    weakSumSquaresWithDrift (prodJet X ζ u D) x =
      weakSumSquaresWithDrift D x * ζ x +
        2 * ∑ i : Fin q, D [i.succ] x * fieldDerivative (X i.succ) ζ x +
          u x * sumSquaresWithDrift X ζ x := by
  have hsum : ∑ i : Fin q, ((D [i.succ, i.succ] x * ζ x +
        D [i.succ] x * fieldDerivative (X i.succ) ζ x) +
      (D [i.succ] x * fieldDerivative (X i.succ) ζ x +
        u x * fieldDerivative (X i.succ) (fieldDerivative (X i.succ) ζ) x)) =
      (∑ i : Fin q, D [i.succ, i.succ] x) * ζ x +
        2 * ∑ i : Fin q, D [i.succ] x * fieldDerivative (X i.succ) ζ x +
          u x * ∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) ζ) x := by
    calc _ = ∑ i : Fin q, (D [i.succ, i.succ] x * ζ x +
          2 * (D [i.succ] x * fieldDerivative (X i.succ) ζ x) +
          u x * fieldDerivative (X i.succ) (fieldDerivative (X i.succ) ζ) x) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
            ← Finset.mul_sum]
  simp only [weakSumSquaresWithDrift, sumSquaresWithDrift, prodJet]
  rw [hsum]
  ring

end RothschildStein.P2

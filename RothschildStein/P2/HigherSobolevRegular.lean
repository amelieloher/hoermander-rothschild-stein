-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevCompact

/-!
# One regularity step on a compactly supported function

Part of the higher Sobolev estimate (BB pp. 590–591, (11.74), corrected: the cutoff is `φ²`, one factor localizing the input and one
the representation). Let `v ∈ W^{j+2,p}_{X̃}(V)` have compact support in `V`, with `a = 1` on `supp v`
(`a` the cutoff of the representation), and suppose `L̃ v = f ∈ W^{j+1,p}_{X̃}(V)`. Then
`v ∈ W^{j+3,p}_{X̃}(V)`; no regularity beyond the hypotheses is presupposed.

Proof. For a word `I' = i :: I''` of length `j + 2`, the higher-order representation on `W^{j+2,p}_0(V)` (`weakExtension_higher`
with the families `S_J = X̃_i G_J`, `T_K = X̃_i H_K` built from the type-1 forms of `I''` of the higher-order representation and
left differentiation `LeftDifferentiation`) gives `X̃_{I'} v = ∑_J S̄_J (X̃_J L̃ v) + ∑_K T̄_K (X̃_K v)` with `|J| ≤ j`,
`|K| ≤ j + 1`. The inputs lie in `W^{1,p}` (`L̃ v = f ∈ W^{j+1,p}`, `v ∈ W^{j+2,p}`) and vanish off
`supp v`, so they lie in `W^{1,p}_{X̃,0}(V)`; by the higher-order gain (`noDrift_sobolev_lp_of_transfer`, `k = 1`) each
`S̄_J (X̃_J L̃ v)` and `T̄_K (X̃_K v)` lies in `W^{1,p}`. So `X̃_{I'} v ∈ W^{1,p}`: `X̃_i X̃_{I'} v ∈ L^p`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Jet

variable {N k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
  {V : Opens (Fin N → ℝ)}

/-- A word derivative of a weak jet lies in a lower Sobolev class: if `D τ` is the weak `X̃_τ`-derivative of
`u` and `|τ| + N' ≤ kk`, then `D τ ∈ W^{N',P}` (all weights one). -/
theorem memSobolevX_jet_word (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) {kk : ℕ} {P : ℝ≥0∞} {u : (Fin N → ℝ) → ℝ}
    {D : List (Fin k) → (Fin N → ℝ) → ℝ} (hD : IsWeakJet w Xt V kk P u D) {τ : List (Fin k)}
    {N' : ℕ} (hτ : τ.length + N' ≤ kk) : memSobolevX w Xt V N' P (D τ) := by
  have hmem : ∀ J ∈ wordFamily w N', J ++ τ ∈ wordFamily w kk := by
    intro J hJ
    rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw] at hJ
    rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
    simp only [List.length_append]
    omega
  refine ⟨(hD τ ?_).2, fun J hJ => ⟨D (J ++ τ), hD.hasWeakWordDeriv_append hXt τ J (hmem J hJ),
    (hD _ (hmem J hJ)).2⟩⟩
  rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
  omega

end Jet

section Regular

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} {q₀ : ℕ}
  {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}

/-- `weakSumSquares D J` lies in `L^P` if the jet `D` has order at least `|J| + 2`. -/
theorem memLp_weakSumSquares (hw : ∀ j, (w j : ℕ) = 1) {kk : ℕ} {P : ℝ≥0∞}
    {v : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsWeakJet w C.Xl F.V kk P v D) {J : List (Fin q)} (hJ : J.length + 2 ≤ kk) :
    MemLp (weakSumSquares D J) P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  have : weakSumSquares D J = fun x => ∑ i : Fin q, D (J ++ [i, i]) x := rfl
  rw [this]
  refine memLp_finsetSum Finset.univ fun i _ => (hD (J ++ [i, i]) ?_).2
  rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **A single endpoint term preserves `W^{1,P}_0` inputs.** If `S' g = X̃_i (T g)` weakly on
tests, with `T` of type 1 and `S'` of type 0, then the bounded extension `S̄'` maps `W^{1,P}_{X̃,0}(V) ∩ L^P(V)`
into `W^{1,P}_{X̃}(V)` (`noDrift_sobolev_lp_of_transfer` with the family `F_l = [l = i] T`). -/
theorem sobolev_one_of_endpoint (hH : HigherFrame C H K hQ F a) {P : ℝ≥0∞} [Fact (1 ≤ P)]
    (hP1 : 1 < P) (hPt : P ≠ ⊤) (T : TypeOperator F 1) (i : Fin q) (S' : TypeOperator F 0)
    (hS : ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv C.Xl F.V [i] (T.apply (g : (Fin (n + m) → ℝ) → ℝ))
        (S'.apply (g : (Fin (n + m) → ℝ) → ℝ)))
    {h : (Fin (n + m) → ℝ) → ℝ} (hh : memSobolevXZero w C.Xl F.V 1 P h)
    (hhL : MemLp h P (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) :
    memSobolevX w C.Xl F.V 1 P (S'.lpAct hH.std hP1 hPt h) := by
  classical
  have hF := hH.std
  have hw := hH.weight
  choose Z hZ using fun l : Fin q => exists_leftOp_of_eq (lam' := 0) hH.hLeftDiff
    (TypeOperator.zero F 1) l (by have := hw l; omega) (by have := hw l; omega)
  let Fj : Fin q → TypeOperator F 1 := fun l => if l = i then T else TypeOperator.zero F 1
  let Tj : Fin q → TypeOperator F 0 := fun l => if l = i then S' else Z l
  have hT : ∀ (l : Fin q) (g : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l] ((Fj l).apply (g : (Fin (n + m) → ℝ) → ℝ))
        ((Tj l).apply (g : (Fin (n + m) → ℝ) → ℝ)) := by
    intro l g
    by_cases hl : l = i
    · subst hl
      simp only [Fj, Tj, ↓reduceIte]
      exact hS g
    · simp only [Fj, Tj, hl, ↓reduceIte]
      exact hZ l g
  obtain ⟨Cg, -, hbound⟩ := LiftedChart.noDrift_sobolev_lp_of_transfer hF hw C.B hH.hRowInt hH.hLeftDiff
    hH.hRightDiff hH.hTransfer Fj Tj hT 1 hP1 hPt
  have hzero : ∀ l : Fin q, l ≠ i → ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞),
      (Z l).apply (g : (Fin (n + m) → ℝ) → ℝ) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
        fun _ => 0 := by
    intro l _ g
    have h1 := hZ l g
    have e : (TypeOperator.zero F 1).apply (g : (Fin (n + m) → ℝ) → ℝ) = fun _ => 0 :=
      funext fun ξ => TypeOperator.apply_zero one_ne_zero _ ξ
    rw [e] at h1
    exact RothschildStein.S.hasWeakWordDeriv_unique C.Xl F.V h1
      (RothschildStein.S.hasWeakWordDeriv_zero C.Xl F.V [l])
  have hSb : ∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞),
      (S'.lpExt hF hP1 hPt) (testToLp F.V hF.lifted.volume_lt_top P φ) =ᵐ[volume.restrict
        (F.V : Set (Fin (n + m) → ℝ))] fun ξ => ∑ l, (Tj l).apply (φ : (Fin (n + m) → ℝ) → ℝ) ξ := by
    intro φ
    have h1 : (S'.lpExt hF hP1 hPt) (testToLp F.V hF.lifted.volume_lt_top P φ) =ᵐ[volume.restrict
        (F.V : Set (Fin (n + m) → ℝ))] S'.apply (φ : (Fin (n + m) → ℝ) → ℝ) :=
      (Classical.choose_spec (S'.exists_lpExt hF hP1 hPt)).1 φ
    have h2 : ∀ᵐ ξ ∂(volume.restrict (F.V : Set (Fin (n + m) → ℝ))), ∀ l : Fin q, l ≠ i →
        (Z l).apply (φ : (Fin (n + m) → ℝ) → ℝ) ξ = 0 :=
      (Filter.eventually_all).2 fun l => by
        by_cases hl : l = i
        · exact Filter.Eventually.of_forall fun _ h => absurd hl h
        · filter_upwards [hzero l hl φ] with ξ hξ _ using hξ
    filter_upwards [h1, h2] with ξ e1 e2
    rw [e1, Finset.sum_eq_single i]
    · simp only [Tj, ↓reduceIte]
    · intro l _ hl
      simp only [Tj, hl, ↓reduceIte]
      exact e2 l hl
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hh' : memSobolevXZero w C.Xl F.V 1 P (⇑(hhL.toLp h)) :=
    (RothschildStein.S.memSobolevXZero_congr_ae C.Xl F.V w 1 P hhL.coeFn_toLp).2 hh
  obtain ⟨hmem, -⟩ := hbound (S'.lpExt hF hP1 hPt) hSb (hhL.toLp h) hh'
  unfold TypeOperator.lpAct
  rw [actLp_eq _ hhL]
  exact hmem

/-- **The words of length `j + 2` of a regular compactly supported `v`.** Let
`v ∈ W^{j+2,P}_{X̃}(V)` have compact support, `a = 1` on `supp v`, and `L̃ v = f ∈ W^{j+1,P}_{X̃}(V)`. For
every word `I'` of length `j + 2` the weak derivative `X̃_{I'} v` exists and lies in `W^{1,P}_{X̃}(V)`. -/
theorem exists_regular_word (hH : HigherFrame C H K hQ F a) {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP1 : 1 < P)
    (hPt : P ≠ ⊤) {j : ℕ} {v f : (Fin (n + m) → ℝ) → ℝ}
    (hv : memSobolevX w C.Xl F.V (j + 2) P v) (hc : HasCompactSupport v)
    (hs : tsupport v ⊆ (F.V : Set (Fin (n + m) → ℝ))) (ha1 : ∀ x ∈ tsupport v, a x = 1)
    (hop : HasWeakOperatorValue C.Xl F.V (noDriftOpWords q) v f)
    (hf : memSobolevX w C.Xl F.V (j + 1) P f) (I' : List (Fin q)) (hI' : I'.length = j + 2) :
    ∃ R : (Fin (n + m) → ℝ) → ℝ, hasWeakWordDeriv C.Xl F.V I' v R ∧
      memSobolevX w C.Xl F.V 1 P R := by
  classical
  have hF := hH.std
  have hw := hH.weight
  have hXt := hH.contDiffOn_Xl
  have hv0 : memSobolevXZero w C.Xl F.V (j + 2) P v :=
    RothschildStein.S.memSobolevXZero_of_compact_support w C.Xl F.V hXt (j + 2) hPt hv hc hs
  obtain ⟨D, hD⟩ := IsWeakJet.exists hv
  obtain ⟨E, hE⟩ := IsWeakJet.exists hf
  have hav : ∀ x, a x * v x = v x := by
    intro x
    by_cases hx : x ∈ tsupport v
    · rw [ha1 x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hvz : ∀ x, x ∉ tsupport v → v x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hDz : ∀ K' ∈ wordFamily w (j + 2), ∀ᵐ x ∂(volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
      x ∉ tsupport v → D K' x = 0 := fun K' hK' =>
    hasWeakWordDeriv_ae_zero_off (isClosed_tsupport v) hvz (hD K' hK').1
  have hK₀ : IsCompact (tsupport v) := hc
  cases I' with
  | nil => simp at hI'
  | cons i I'' =>
    have hI''len : I''.length = j + 1 := by simpa using hI'
    have hI'2 : 2 ≤ (i :: I'').length := by
      rw [hI']; omega
    obtain ⟨G, Hf, hGH⟩ := hasRepForm_length hXt hw C.B hH.hRowInt hH.hLeftDiff hH.hRightDiff hH.hTransfer
      hH.density_smooth hH.density_pos a hH.hParametrix I'' (by omega)
    choose Sop hSop using fun T : TypeOperator F 1 => exists_leftOp_of_eq (lam' := 0) hH.hLeftDiff T i
      (by have := hw i; omega) (by have := hw i; omega)
    have hid : ∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv C.Xl F.V (i :: I'') (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords q ((i :: I'').length - 2),
              (Sop (G J)).apply (wordDerivative C.Xl J (sumSquares C.Xl (u : (Fin (n + m) → ℝ) → ℝ))) ξ) +
            ∑ K' ∈ repWords q ((i :: I'').length - 1),
              (Sop (Hf K')).apply (wordDerivative C.Xl K' (u : (Fin (n + m) → ℝ) → ℝ)) ξ) := by
      intro u
      have h1 := repWeak_finset_sum hXt [i] (repWords q (I''.length - 1))
        (fun J ξ => (G J).apply
          (wordDerivative C.Xl J (repSumSquaresTest F C.Xl hXt u : (Fin (n + m) → ℝ) → ℝ)) ξ)
        (fun J ξ => (Sop (G J)).apply
          (wordDerivative C.Xl J (repSumSquaresTest F C.Xl hXt u : (Fin (n + m) → ℝ) → ℝ)) ξ)
        (fun J _ => hSop (G J) (RothschildStein.S.wordDerivativeTest F.V C.Xl hXt J
          (repSumSquaresTest F C.Xl hXt u)))
      have h2 := repWeak_finset_sum hXt [i] (repWords q I''.length)
        (fun K' ξ => (Hf K').apply (wordDerivative C.Xl K' (u : (Fin (n + m) → ℝ) → ℝ)) ξ)
        (fun K' ξ => (Sop (Hf K')).apply (wordDerivative C.Xl K' (u : (Fin (n + m) → ℝ) → ℝ)) ξ)
        (fun K' _ => hSop (Hf K') (RothschildStein.S.wordDerivativeTest F.V C.Xl hXt K' u))
      have h3 := (RothschildStein.S.hasWeakWordDeriv_cons_iff C.Xl F.V hXt (hGH u) i).mpr
        (RothschildStein.S.hasWeakWordDeriv_add C.Xl F.V hXt h1 h2)
      simp only [List.length_cons, coe_repSumSquaresTest] at h3 ⊢
      exact h3
    have hex := LiftedChart.weakExtension_higher hF hw (i :: I'') hI'2 hid hP1 hPt
      (by rw [hI']; exact hv0) (by rw [hI']; exact hD)
    rw [show (fun x => a x * v x) = v from funext hav] at hex
    refine ⟨_, hex, ?_⟩
    have hlen2 : (i :: I'').length - 2 = j := by rw [hI']; omega
    have hlen1 : (i :: I'').length - 1 = j + 1 := by rw [hI']; omega
    rw [hlen2, hlen1]
    have hJterm : ∀ J ∈ repWords q j, memSobolevX w C.Xl F.V 1 P
        ((Sop (G J)).lpAct hF hP1 hPt (weakSumSquares D J)) := by
      intro J hJ
      have hJl : J.length ≤ j := mem_repWords.1 hJ
      have hJmem : J ∈ wordFamily w (j + 1) := by
        rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]; omega
      have hfJ : hasWeakWordDeriv C.Xl F.V J f (weakSumSquares D J) :=
        hasWeakWordDeriv_operator_value hw hXt hD hop J (by omega)
      have hae : weakSumSquares D J =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] E J :=
        RothschildStein.S.hasWeakWordDeriv_unique C.Xl F.V hfJ (hE J hJmem).1
      have hmem1 : memSobolevX w C.Xl F.V 1 P (weakSumSquares D J) :=
        (RothschildStein.S.memSobolevX_congr_ae C.Xl F.V w 1 P hae).2
          (memSobolevX_jet_word hXt hw hE (τ := J) (N' := 1) (by omega))
      have hz : ∀ᵐ x ∂(volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
          x ∉ tsupport v → weakSumSquares D J x = 0 := by
        have hall : ∀ i' : Fin q, ∀ᵐ x ∂(volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
            x ∉ tsupport v → D (J ++ [i', i']) x = 0 := fun i' =>
          hDz _ (by rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
                    simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        filter_upwards [(Filter.eventually_all).2 hall] with x hx hxs
        exact Finset.sum_eq_zero fun i' _ => hx i' hxs
      exact sobolev_one_of_endpoint hH hP1 hPt (G J) i (Sop (G J)) (hSop (G J))
        (memSobolevXZero_of_zero_off hXt hK₀ hs hPt hmem1 hz) (memLp_weakSumSquares hw hD (by omega))
    have hKterm : ∀ K' ∈ repWords q (j + 1), memSobolevX w C.Xl F.V 1 P
        ((Sop (Hf K')).lpAct hF hP1 hPt (D K')) := by
      intro K' hK'
      have hKl : K'.length ≤ j + 1 := mem_repWords.1 hK'
      have hKmem : K' ∈ wordFamily w (j + 2) := by
        rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]; omega
      have hmem1 : memSobolevX w C.Xl F.V 1 P (D K') :=
        memSobolevX_jet_word hXt hw hD (τ := K') (N' := 1) (by omega)
      exact sobolev_one_of_endpoint hH hP1 hPt (Hf K') i (Sop (Hf K')) (hSop (Hf K'))
        (memSobolevXZero_of_zero_off hXt hK₀ hs hPt hmem1 (hDz K' hKmem)) (hD K' hKmem).2
    exact memSobolevX_add' hXt (memSobolevX_finset_sum hXt _ hJterm)
      (memSobolevX_finset_sum hXt _ hKterm)

/-- **One regularity step** (BB pp. 590-591): a compactly supported
`v ∈ W^{j+2,P}_{X̃}(V)` with `a = 1` on `supp v` and `L̃ v = f ∈ W^{j+1,P}_{X̃}(V)` lies in
`W^{j+3,P}_{X̃}(V)`. Conditional exactly on `HigherFrame`. -/
theorem regularityStep (hH : HigherFrame C H K hQ F a) {P : ℝ≥0∞} (hP1 : 1 < P) (hPt : P ≠ ⊤)
    (j : ℕ) {v f : (Fin (n + m) → ℝ) → ℝ} (hv : memSobolevX w C.Xl F.V (j + 2) P v)
    (hc : HasCompactSupport v) (hs : tsupport v ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (ha1 : ∀ x ∈ tsupport v, a x = 1) (hop : HasWeakOperatorValue C.Xl F.V (noDriftOpWords q) v f)
    (hf : memSobolevX w C.Xl F.V (j + 1) P f) : memSobolevX w C.Xl F.V (j + 3) P v := by
  have : Fact (1 ≤ P) := ⟨hP1.le⟩
  have hw := hH.weight
  have hXt := hH.contDiffOn_Xl
  refine ⟨hv.1, fun I hI => ?_⟩
  rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw] at hI
  by_cases hlen : I.length ≤ j + 2
  · refine hv.2 I ?_
    rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
    exact hlen
  · cases I with
    | nil => simp at hlen
    | cons i I' =>
      have hI' : I'.length = j + 2 := by
        simp only [List.length_cons] at hI hlen
        omega
      obtain ⟨R, hR, hRs⟩ := exists_regular_word hH hP1 hPt hv hc hs ha1 hop hf I' hI'
      obtain ⟨g, hg, hgL⟩ := hRs.2 [i] (by
        rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
        simp)
      exact ⟨g, (RothschildStein.S.hasWeakWordDeriv_cons_iff C.Xl F.V hXt hR i).2 hg, hgL⟩

end Regular

end RothschildStein.P2

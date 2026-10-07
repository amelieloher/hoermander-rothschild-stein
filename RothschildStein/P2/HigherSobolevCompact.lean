-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevSupport
public import RothschildStein.P1.WeakExtensionMain
public import RothschildStein.P1.HigherNormSobolev
public import RothschildStein.P1.HigherNormHolderJets
public import RothschildStein.P1.GainHolder
public import RothschildStein.P1.StandardFrame

/-!
# The higher no-drift recurrence for compactly supported functions

Part of the higher Sobolev estimate (BB pp. 588–589, Prop 11.46, corrected: the forcing norm is
`W^{k,p}`, not `L^p`). For a
standard frame of a lifted no-drift chart and a cutoff `a` as in the higher-order representation, every compactly supported
`v ∈ W^{k+2,p}_{X̃}(V)` with `a = 1` on `supp v` satisfies
`‖v‖_{W^{k+2,p}} ≤ C(A, p, k) (‖L̃ v‖_{W^{k,p}} + ‖v‖_{W^{k+1,p}})`.

Proof. `v ∈ W^{k+2,p}_0(V)`. By the higher-order representation on `W^{m,p}_0` (`weakExtension_higher_full_of`, the weak extension theorem),
for every word `I` of length `k + 2`, `X̃_I v = X̃_I (a v) = ∑_J S̄_IJ (X̃_J L̃ v) + ∑_K T̄_IK (X̃_K v)` weakly,
with `|J| ≤ k`, `|K| ≤ k + 1` and bounded `L^p` operators `S̄, T̄` (the continuity theorem); the weak jet of `v` makes
`X̃_J L̃ v = ∑_i D (J ++ [i, i])` the weak derivative of `L̃ v`.

`HigherFrame` is the bundle of the operator and geometric hypotheses (`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`,
`DerivativeTransfer` of the type calculus and the signed parametrix `SignedParametrixNoDrift`) for a standard frame of a
lifted no-drift chart together with a cutoff `a = 1` near the chart centre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

section Frame

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- **The hypotheses of the no-drift higher regularity at a chart.** For a lifted
no-drift chart `C` (all weights one), a standard frame `F` of `C` (kernel `K` of the model `H`), and a
cutoff `a ∈ C_c^∞(F.V)` equal to one near the centre `(x₀, 0)`: the type-calculus statements
`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation` and `DerivativeTransfer` (for the basis words `C.B` of the
chart) for the frame, and the signed parametrix (`SignedParametrixNoDrift` with the density `C.c`) for the
cutoff `a` and every `b`. -/
structure HigherFrame (C : LiftedChart w s Ω hΩ X x₀ m) {q₀ : ℕ} (H : H1.StandingHypotheses C.G q₀)
    (K : H1.FundamentalKernel C.G H) (hQ : 2 < (C.G.homogeneousDimension : ℝ))
    (F : KernelFrame (n + m)) (a : TestFunction F.V ℝ (⊤ : ℕ∞)) : Prop where
  std : C.IsStandardFrame F H K hQ
  weight : ∀ j, (w j : ℕ) = 1
  hRowInt : TypeKernelIntegrable F
  hLeftDiff : LeftDifferentiation F w C.Xl
  hRightDiff : RightDifferentiation F w C.Xl std.lifted.contDiffOn_Xl
  hTransfer : DerivativeTransfer F w C.Xl C.B
  hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl C.c a b
  near : ∀ᶠ x in 𝓝 (joinPoint x₀ (0 : Fin m → ℝ)),
    x ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ a x = 1

variable {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} {q₀ : ℕ}
  {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}

theorem HigherFrame.contDiffOn_Xl (hH : HigherFrame C H K hQ F a) :
    ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
  hH.std.lifted.contDiffOn_Xl

theorem HigherFrame.density_smooth (hH : HigherFrame C H K hQ F a) :
    ContDiffOn ℝ (⊤ : ℕ∞) C.c (F.V : Set (Fin (n + m) → ℝ)) :=
  C.density_smooth.mono hH.std.lifted.subset_U

theorem HigherFrame.density_pos (hH : HigherFrame C H K hQ F a) :
    ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < C.c ξ :=
  fun ξ hξ => C.density_pos ξ (hH.std.lifted.subset_U hξ)

/-! ### `L^P` bounds of the extended operators -/

/-- `‖T̄ g‖_P ≤ ‖T̄‖ ‖g‖_P` for the bounded extension of a type-`λ` operator. -/
theorem eLpNorm_lpAct_le {lam : ℕ} {P : ℝ≥0∞} [Fact (1 ≤ P)]
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam) (hP1 : 1 < P) (hPt : P ≠ ⊤)
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : MemLp g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) :
    eLpNorm (T.lpAct hF hP1 hPt g) P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
      ‖T.lpExt hF hP1 hPt‖ₑ *
        eLpNorm g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  unfold TypeOperator.lpAct
  rw [actLp_eq _ hg, ← Lp.enorm_toLp hg, ← Lp.enorm_def]
  exact ContinuousLinearMap.le_opENorm _ _

end Frame

section Words

variable {N k : ℕ} {w : Fin k → ℕ+}

/-- For all weights one, the words of length at most `j` are the words of weight at most `j`. -/
theorem repWords_eq_wordFamily (hw : ∀ j, (w j : ℕ) = 1) (j : ℕ) : repWords k j = wordFamily w j := by
  ext J
  rw [mem_repWords, RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length hw]

end Words

section CompactRecurrence

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} {q₀ : ℕ}
  {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}

/-- **Per-word bound.** For a word `I` of length at least two there is a
finite constant `Λ_I` such that, for `v ∈ W^{|I|,P}_{X̃,0}(F.V)` with weak jet `D` and `a v = v`, the weak
derivative `X̃_I v` is represented by a function `g` with
`‖g‖_P ≤ Λ_I (∑_{|J| ≤ |I|-2} ‖X̃_J L̃ v‖_P + ∑_{|K| ≤ |I|-1} ‖X̃_K v‖_P)` (the extended higher-order representation
with the bounded `L^p` extensions of the continuity theorem). -/
theorem exists_wordBound (hH : HigherFrame C H K hQ F a) {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP1 : 1 < P)
    (hPt : P ≠ ⊤) (I : List (Fin q)) (hI : 2 ≤ I.length) :
    ∃ Λ : ℝ≥0∞, Λ ≠ ⊤ ∧
      ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V I.length P v → IsWeakJet w C.Xl F.V I.length P v D →
        (∀ x, a x * v x = v x) →
        ∃ g : (Fin (n + m) → ℝ) → ℝ, hasWeakWordDeriv C.Xl F.V I v g ∧
          eLpNorm g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
            Λ * ((∑ J ∈ repWords q (I.length - 2),
                eLpNorm (weakSumSquares D J) P (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) +
              ∑ K' ∈ repWords q (I.length - 1),
                eLpNorm (D K') P (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) := by
  have hF := hH.std
  have hw := hH.weight
  obtain ⟨Sf, Tf, -, -, -, -, hext, -⟩ := LiftedChart.weakExtension_higher_full_of hF hw C.B hH.hRowInt
    hH.hLeftDiff hH.hRightDiff hH.hTransfer hH.density_smooth hH.density_pos a hH.hParametrix I hI
  set μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ)) with hμ
  let M : ℝ≥0∞ := (∑ J ∈ repWords q (I.length - 2), ‖(Sf J).lpExt hF hP1 hPt‖ₑ) +
    ∑ K' ∈ repWords q (I.length - 1), ‖(Tf K').lpExt hF hP1 hPt‖ₑ
  refine ⟨M, ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun J _ => enorm_ne_top,
    ENNReal.sum_ne_top.2 fun K' _ => enorm_ne_top⟩, fun v D hv hD hav => ?_⟩
  have hex := hext P hP1 hPt v D hv hD
  have hfun : (fun x => a x * v x) = v := funext hav
  rw [hfun] at hex
  refine ⟨_, hex, ?_⟩
  have hSmem : ∀ J ∈ repWords q (I.length - 2), MemLp (weakSumSquares D J) P μ := by
    intro J hJ
    have hJ' := mem_repWords.1 hJ
    have : weakSumSquares D J = fun x => ∑ i : Fin q, D (J ++ [i, i]) x := rfl
    rw [this]
    refine memLp_finsetSum Finset.univ fun i _ => (hD (J ++ [i, i]) ?_).2
    rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hTmem : ∀ K' ∈ repWords q (I.length - 1), MemLp (D K') P μ := by
    intro K' hK'
    have hK'' := mem_repWords.1 hK'
    refine (hD K' ?_).2
    rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
    omega
  have hSle : ∀ J ∈ repWords q (I.length - 2), ‖(Sf J).lpExt hF hP1 hPt‖ₑ ≤ M := fun J hJ =>
    (Finset.single_le_sum (f := fun J => ‖(Sf J).lpExt hF hP1 hPt‖ₑ) (fun _ _ => zero_le) hJ).trans
      le_self_add
  have hTle : ∀ K' ∈ repWords q (I.length - 1), ‖(Tf K').lpExt hF hP1 hPt‖ₑ ≤ M := fun K' hK' =>
    (Finset.single_le_sum (f := fun K' => ‖(Tf K').lpExt hF hP1 hPt‖ₑ) (fun _ _ => zero_le) hK').trans
      le_add_self
  have hP1' : (1 : ℝ≥0∞) ≤ P := hP1.le
  have h1 : eLpNorm (fun ξ => ∑ J ∈ repWords q (I.length - 2),
      (Sf J).lpAct hF hP1 hPt (weakSumSquares D J) ξ) P μ ≤
      M * ∑ J ∈ repWords q (I.length - 2), eLpNorm (weakSumSquares D J) P μ := by
    have e : (fun ξ => ∑ J ∈ repWords q (I.length - 2), (Sf J).lpAct hF hP1 hPt (weakSumSquares D J) ξ) =
        ∑ J ∈ repWords q (I.length - 2), (Sf J).lpAct hF hP1 hPt (weakSumSquares D J) := by
      funext ξ; simp [Finset.sum_apply]
    rw [e, Finset.mul_sum]
    refine (eLpNorm_sum_le hP1').trans (Finset.sum_le_sum fun J hJ => ?_)
    exact (eLpNorm_lpAct_le hF (Sf J) hP1 hPt (hSmem J hJ)).trans (mul_le_mul' (hSle J hJ) le_rfl)
  have h2 : eLpNorm (fun ξ => ∑ K' ∈ repWords q (I.length - 1),
      (Tf K').lpAct hF hP1 hPt (D K') ξ) P μ ≤
      M * ∑ K' ∈ repWords q (I.length - 1), eLpNorm (D K') P μ := by
    have e : (fun ξ => ∑ K' ∈ repWords q (I.length - 1), (Tf K').lpAct hF hP1 hPt (D K') ξ) =
        ∑ K' ∈ repWords q (I.length - 1), (Tf K').lpAct hF hP1 hPt (D K') := by
      funext ξ; simp [Finset.sum_apply]
    rw [e, Finset.mul_sum]
    refine (eLpNorm_sum_le hP1').trans (Finset.sum_le_sum fun K' hK' => ?_)
    exact (eLpNorm_lpAct_le hF (Tf K') hP1 hPt (hTmem K' hK')).trans (mul_le_mul' (hTle K' hK') le_rfl)
  calc eLpNorm (fun ξ => ∑ J ∈ repWords q (I.length - 2),
          (Sf J).lpAct hF hP1 hPt (weakSumSquares D J) ξ +
        ∑ K' ∈ repWords q (I.length - 1), (Tf K').lpAct hF hP1 hPt (D K') ξ) P μ
      ≤ eLpNorm (fun ξ => ∑ J ∈ repWords q (I.length - 2),
          (Sf J).lpAct hF hP1 hPt (weakSumSquares D J) ξ) P μ +
        eLpNorm (fun ξ => ∑ K' ∈ repWords q (I.length - 1),
          (Tf K').lpAct hF hP1 hPt (D K') ξ) P μ := eLpNorm_add_le hP1'
    _ ≤ M * ∑ J ∈ repWords q (I.length - 2), eLpNorm (weakSumSquares D J) P μ +
        M * ∑ K' ∈ repWords q (I.length - 1), eLpNorm (D K') P μ := add_le_add h1 h2
    _ = _ := by rw [mul_add]

/-- A weak jet of `v` of order `j + 2` makes `weakSumSquares D J` (`|J| ≤ j`) the weak `X̃_J`-derivative
of any representative `f` of `L̃ v`. -/
theorem hasWeakWordDeriv_operator_value (hw : ∀ j, (w j : ℕ) = 1)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)))
    {P : ℝ≥0∞} {kk : ℕ} {v f : (Fin (n + m) → ℝ) → ℝ}
    {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ} (hD : IsWeakJet w C.Xl F.V kk P v D)
    (hop : HasWeakOperatorValue C.Xl F.V (noDriftOpWords q) v f) (J : List (Fin q))
    (hJ : J.length + 2 ≤ kk) :
    hasWeakWordDeriv C.Xl F.V J f (weakSumSquares D J) := by
  obtain ⟨g, hg, hf⟩ := hop
  have hgD : ∀ i, g i =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] D [i, i] := fun i =>
    RothschildStein.S.hasWeakWordDeriv_unique C.Xl F.V (hg i)
      (hD [i, i] (by
        rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
        have : 2 ≤ kk := by omega
        simpa using this)).1
  have hae : f =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] weakSumSquares D [] := by
    have h2 : (fun x => ∑ i, g i x) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
        weakSumSquares D [] := by
      have := (Filter.eventually_all (ι := Fin q)).2 hgD
      filter_upwards [this] with x hx
      simp only [weakSumSquares, List.nil_append]
      exact Finset.sum_congr rfl fun i _ => hx i
    exact hf.trans h2
  exact RothschildStein.S.hasWeakWordDeriv_congr_ae C.Xl F.V (hD.hasWeakWordDeriv_sumSquares hXt hw J hJ)
    hae.symm Filter.EventuallyEq.rfl

/-- **The compact recurrence** (BB p. 589, Prop 11.46, with the corrected `W^{k,p}` data norm).
Under the hypotheses `HigherFrame` and `1 < P < ∞`, for every `j` there is `Λ > 0` such that every `v ∈ W^{j+2,P}_{X̃}(V)`
with compact support in `V` and `a = 1` on `supp v`, and every value `f = L̃ v` of the operator,
`‖v‖_{W^{j+2,P}} ≤ Λ (‖f‖_{W^{j,P}} + ‖v‖_{W^{j+1,P}})`. -/
theorem compactRecurrence (hH : HigherFrame C H K hQ F a) {P : ℝ≥0∞} (hP1 : 1 < P) (hPt : P ≠ ⊤)
    (j : ℕ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ v f : (Fin (n + m) → ℝ) → ℝ,
      memSobolevX w C.Xl F.V (j + 2) P v → HasCompactSupport v →
      tsupport v ⊆ (F.V : Set (Fin (n + m) → ℝ)) → (∀ x ∈ tsupport v, a x = 1) →
      HasWeakOperatorValue C.Xl F.V (noDriftOpWords q) v f →
      sobolevXENorm w C.Xl F.V (j + 2) P v ≤
        ENNReal.ofReal Λ * (sobolevXENorm w C.Xl F.V j P f +
          sobolevXENorm w C.Xl F.V (j + 1) P v) := by
  have : Fact (1 ≤ P) := ⟨hP1.le⟩
  have hw := hH.weight
  have hXt := hH.contDiffOn_Xl
  choose! Λ hΛ hbd using fun (I : List (Fin q)) (hI : 2 ≤ I.length) =>
    exists_wordBound hH hP1 hPt I hI
  let S2 : Finset (List (Fin q)) := (wordFamily w (j + 2)).filter fun I => ¬ I.length ≤ j + 1
  have hS2 : ∀ I ∈ S2, I.length = j + 2 := by
    intro I hI
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hI
    rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw] at h1
    omega
  have hLfin : (1 + ∑ I ∈ S2, Λ I) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun I hI =>
      hΛ I (by have := hS2 I hI; omega)⟩
  refine ⟨(1 + ∑ I ∈ S2, Λ I).toReal, ENNReal.toReal_pos (by simp) hLfin,
    fun v f hv hc hs ha1 hop => ?_⟩
  rw [ENNReal.ofReal_toReal hLfin]
  have hv0 : memSobolevXZero w C.Xl F.V (j + 2) P v :=
    RothschildStein.S.memSobolevXZero_of_compact_support w C.Xl F.V hXt (j + 2) hPt hv hc hs
  obtain ⟨D, hD⟩ := IsWeakJet.exists hv
  have hav : ∀ x, a x * v x = v x := by
    intro x
    by_cases hx : x ∈ tsupport v
    · rw [ha1 x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hfD : ∀ J ∈ wordFamily w j, hasWeakWordDeriv C.Xl F.V J f (weakSumSquares D J) := by
    intro J hJ
    rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw] at hJ
    exact hasWeakWordDeriv_operator_value hw hXt hD hop J (by omega)
  have hfsum : ∑ J ∈ repWords q j,
      eLpNorm (weakSumSquares D J) P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) =
      sobolevXENorm w C.Xl F.V j P f := by
    rw [repWords_eq_wordFamily hw j]
    unfold sobolevXENorm
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [RothschildStein.S.weakWordENorm_eq C.Xl F.V J P f _ (hfD J hJ)]
  have hDv : ∀ K' ∈ wordFamily w (j + 1), hasWeakWordDeriv C.Xl F.V K' v (D K') := by
    intro K' hK'
    refine (hD K' ?_).1
    rw [RothschildStein.S.mem_wordFamily_iff] at hK' ⊢
    omega
  have hvsum : ∑ K' ∈ repWords q (j + 1),
      eLpNorm (D K') P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) =
      sobolevXENorm w C.Xl F.V (j + 1) P v := by
    rw [repWords_eq_wordFamily hw (j + 1)]
    unfold sobolevXENorm
    refine Finset.sum_congr rfl fun K' hK' => ?_
    rw [RothschildStein.S.weakWordENorm_eq C.Xl F.V K' P v _ (hDv K' hK')]
  set T : ℝ≥0∞ := sobolevXENorm w C.Xl F.V j P f + sobolevXENorm w C.Xl F.V (j + 1) P v with hT
  have hword : ∀ I ∈ S2, weakWordENorm C.Xl F.V I P v ≤ Λ I * T := by
    intro I hI
    have hIl := hS2 I hI
    obtain ⟨g, hg, hgb⟩ := hbd I (by omega) v D (by rw [hIl]; exact hv0) (by rw [hIl]; exact hD) hav
    rw [RothschildStein.S.weakWordENorm_eq C.Xl F.V I P v g hg]
    refine hgb.trans (mul_le_mul' le_rfl ?_)
    have e1 : I.length - 2 = j := by omega
    have e2 : I.length - 1 = j + 1 := by omega
    rw [e1, e2, hfsum, hvsum]
  have hsplit := Finset.sum_filter_add_sum_filter_not (wordFamily w (j + 2))
    (fun I : List (Fin q) => I.length ≤ j + 1) (fun I => weakWordENorm C.Xl F.V I P v)
  have hlow : (wordFamily w (j + 2)).filter (fun I : List (Fin q) => I.length ≤ j + 1) =
      wordFamily w (j + 1) := by
    ext I
    rw [Finset.mem_filter, RothschildStein.S.mem_wordFamily_iff, RothschildStein.S.mem_wordFamily_iff,
      wordWeight_eq_length' hw]
    omega
  rw [hlow] at hsplit
  have hv1 : sobolevXENorm w C.Xl F.V (j + 1) P v ≤ T := le_add_self
  calc sobolevXENorm w C.Xl F.V (j + 2) P v
      = ∑ I ∈ wordFamily w (j + 2), weakWordENorm C.Xl F.V I P v := rfl
    _ = sobolevXENorm w C.Xl F.V (j + 1) P v + ∑ I ∈ S2, weakWordENorm C.Xl F.V I P v := by
        rw [← hsplit]; rfl
    _ ≤ T + ∑ I ∈ S2, Λ I * T := add_le_add hv1 (Finset.sum_le_sum hword)
    _ = (1 + ∑ I ∈ S2, Λ I) * T := by rw [← Finset.sum_mul, add_mul, one_mul]

end CompactRecurrence

end RothschildStein.P2

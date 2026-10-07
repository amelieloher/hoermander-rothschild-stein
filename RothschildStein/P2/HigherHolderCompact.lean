-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderJets

/-!
# Higher Hölder regularity of compactly supported functions

Part of the higher Hölder estimate (BB pp. 603–604, (11.94)–(11.96): the compact recurrence, with
regularity not presupposed), no drift, alphabet `Fin k` with all weights one, `L̃ = ∑ᵢ X̃ᵢ²` (`weakSumSquares D []`).

Let `v` be compactly supported in the patch `V` of a standard frame with `a v = v`, with a Hölder weak jet `D`
of order `j + 1`, and let `Df` be a Hölder weak jet of order `j` of a function `f = L̃ v` (`weakSumSquares D [] =
Df []` on `V`). Then `v` has a Hölder weak jet of order `j + 2` and
`‖v‖_{C^{j+2,α}(V)} ≤ Λ (‖f‖_{C^{j,α}(V)} + ‖v‖_{C^{j+1,α}(V)})` (`compact_regularity`).

*Proof.* For a word `I = i :: I'` of length `j + 2`, the weak extension of the higher-order
representation (`weakExtension_higher_full_of_lifted`, at the word `I'` of length `j + 1`) gives the weak identity
`X̃_{I'} v = ∑_J S_{I'J} (X̃_J L̃ v) + ∑_K T_{I'K} (X̃_K v)` (`|J| ≤ j - 1`, `|K| ≤ j`, endpoint type-0
operators, pointwise actions, continuous right-hand side), which only involves jets of `v` of order `j + 1`.
The inputs `X̃_J L̃ v` are the entries `Df J` of the jet of `f` (they agree with `weakSumSquares D J`).
Differentiating once more through the endpoint structure (`HigherHolder.endpointDiff_holder`: the commutation
formula and left differentiation) produces type-0 operators of the entries `Df J, Df (l :: J), D K,
D (l :: K)`, of orders `≤ j` and `≤ j + 1`; they are `C^α` by the continuity theorem. Hence `X̃_i X̃_{I'} v` is a continuous
weak derivative, bounded in `C^α(V)` by the right-hand side. No regularity of `v` beyond order `j + 1` is
used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

/-- **The hypotheses of the no-drift higher Hölder regularity at a chart.** For a lifted
chart `C` with all weights one, a standard frame `F` of `C` (kernel `K` of the model `H`) and a cutoff
`a ∈ C_c^∞(F.V)`: the type-calculus statements `TypeKernelIntegrable` (row integrability), `LeftDifferentiation`,
`RightDifferentiation` (differentiation) and `DerivativeTransfer` (transfer, for the basis words `C.B`) for the frame, and the
signed parametrix `SignedParametrixNoDrift` (with the density `C.c`) for the cutoff `a` and every `b`. -/
structure HolderFrame {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
    (C : LiftedChart w s Ω hΩ X x₀ m) {r : ℕ} (H : H1.StandingHypotheses C.G r)
    (K : H1.FundamentalKernel C.G H) (hQ : 2 < (C.G.homogeneousDimension : ℝ))
    (F : KernelFrame (n + m)) (a : TestFunction F.V ℝ (⊤ : ℕ∞)) : Prop where
  std : C.IsStandardFrame F H K hQ
  weight : ∀ j, (w j : ℕ) = 1
  hRowInt : TypeKernelIntegrable F
  hLeftDiff : LeftDifferentiation F w C.Xl
  hRightDiff : RightDifferentiation F w C.Xl std.lifted.contDiffOn_Xl
  hTransfer : DerivativeTransfer F w C.Xl C.B
  hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl C.c a b

section Frame

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}

theorem HolderFrame.density_smooth (hH : HolderFrame C H K hQ F a) :
    ContDiffOn ℝ (⊤ : ℕ∞) C.c (F.V : Set (Fin (n + m) → ℝ)) :=
  C.density_smooth.mono hH.std.lifted.subset_U

theorem HolderFrame.density_pos (hH : HolderFrame C H K hQ F a) :
    ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < C.c ξ :=
  fun ξ hξ => C.density_pos ξ (hH.std.lifted.subset_U hξ)

theorem HolderFrame.comm (hH : HolderFrame C H K hQ F a) : RepComm F C.Xl :=
  repComm_of_transfer hH.std.lifted.contDiffOn_Xl hH.weight C.B hH.hRowInt hH.hRightDiff hH.hTransfer


/-- Arithmetic: `a x + b y ≤ (1 + a + b) (x + y)` for nonnegative `a, b`. -/
theorem ofReal_mul_add_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (x y : ℝ≥0∞) :
    ENNReal.ofReal A * x + ENNReal.ofReal B * y ≤ ENNReal.ofReal (1 + A + B) * (x + y) := by
  calc ENNReal.ofReal A * x + ENNReal.ofReal B * y
      ≤ ENNReal.ofReal A * (x + y) + ENNReal.ofReal B * (x + y) :=
        add_le_add (mul_le_mul' le_rfl le_self_add) (mul_le_mul' le_rfl le_add_self)
    _ = ENNReal.ofReal (A + B) * (x + y) := by
        rw [← add_mul, ENNReal.ofReal_add hA hB]
    _ ≤ ENNReal.ofReal (1 + A + B) * (x + y) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

/-- The entry `D J` and the entries `D ([l] ++ J)` are distinct words of weight at most `N`, so their
norms add up to at most the norm of the jet of order `N`. -/
theorem jetEntry_norm_le (hw : ∀ j, (w j : ℕ) = 1) {n' : ℕ}
    (d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞) (V : Set (Fin n' → ℝ)) (α : ℝ) {N : ℕ}
    {J : List (Fin k)} (hJ : J.length + 1 ≤ N) (D : List (Fin k) → (Fin n' → ℝ) → ℝ) :
    holderENorm d α V (D J) + ∑ l : Fin k, holderENorm d α V (D ([l] ++ J)) ≤
      holderJetNorm w d V α N D := by
  classical
  have hsub : insert J (Finset.univ.image fun l : Fin k => [l] ++ J) ⊆ wordFamily w N := by
    intro K' hK'
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
    rcases Finset.mem_insert.1 hK' with rfl | h
    · omega
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 h
      simp only [List.singleton_append, List.length_cons]
      omega
  have hnot : J ∉ Finset.univ.image fun l : Fin k => [l] ++ J := by
    intro h
    obtain ⟨l, -, hl⟩ := Finset.mem_image.1 h
    have := congrArg List.length hl
    simp at this
  have hinj : Function.Injective fun l : Fin k => [l] ++ J := fun l l' h => by simpa using h
  calc holderENorm d α V (D J) + ∑ l : Fin k, holderENorm d α V (D ([l] ++ J))
      = ∑ K' ∈ insert J (Finset.univ.image fun l : Fin k => [l] ++ J), holderENorm d α V (D K') := by
        rw [Finset.sum_insert hnot, Finset.sum_image (fun l _ l' _ h => hinj h)]
    _ ≤ holderJetNorm w d V α N D := Finset.sum_le_sum_of_subset hsub

/-- **The per-word regularity and estimate.** For a word
`I` of length `j' + 3` there is `Λ_I > 0` such that for `v` compactly supported in `V` with `a v = v` and a
Hölder weak jet `D` of order `j' + 2`, and a Hölder weak jet `Df` of order `j' + 1` of `f = Df []` with
`L̃ v = ∑ᵢ D [i, i] = f` on `V`, the weak derivative `X̃_I v` exists, is continuous on `V`, and has
`‖X̃_I v‖_{C^α(V)} ≤ Λ_I (‖Df‖_{j' + 1} + ‖D‖_{j' + 2})`. -/
theorem exists_wordRegularity (hH : HolderFrame C H K hQ F a) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (j' : ℕ) {I : List (Fin k)} (hI : I.length = j' + 3) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ (v : (Fin (n + m) → ℝ) → ℝ)
      (D Df : List (Fin k) → (Fin (n + m) → ℝ) → ℝ) (K₀ : Set (Fin (n + m) → ℝ)),
      IsCompact K₀ → K₀ ⊆ (F.V : Set (Fin (n + m) → ℝ)) →
      (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ K₀ → v x = 0) → (∀ x, a x * v x = v x) →
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) v ≠ ⊤ →
      LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V (j' + 2) α v D →
      LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V (j' + 1) α (Df []) Df →
      (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), weakSumSquares D [] x = Df [] x) →
      ∃ g : (Fin (n + m) → ℝ) → ℝ, hasWeakWordDeriv C.Xl F.V I v g ∧
        ContinuousOn g (F.V : Set (Fin (n + m) → ℝ)) ∧
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≤ ENNReal.ofReal Λ *
          (holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 1) Df +
            holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 2) D) := by
  classical
  have hF := hH.std
  have hw := hH.weight
  have hXt := hF.lifted.contDiffOn_Xl
  obtain ⟨i, I', rfl⟩ : ∃ (i : Fin k) (I' : List (Fin k)), I = i :: I' := by
    cases I with
    | nil => simp at hI
    | cons i I' => exact ⟨i, I', rfl⟩
  have hI' : I'.length = j' + 2 := by simpa using hI
  have h2 : I'.length - 2 = j' := by omega
  have h1 : I'.length - 1 = j' + 1 := by omega
  obtain ⟨Sf, Tf, hSend, hTend, -, -, -, hext⟩ := LiftedChart.weakExtension_higher_full_of_lifted hF
    hw C.B hH.hRowInt hH.hLeftDiff hH.hRightDiff hH.hTransfer hH.density_smooth hH.density_pos a hH.hParametrix I' (by omega)
  choose rS QS QS0 ΛS hΛS hdS using fun J : List (Fin k) =>
    endpointDiff_holder hF hw hH.hLeftDiff hH.comm hα0 hα1 (hSend J) i
  choose rT QT QT0 ΛT hΛT hdT using fun K' : List (Fin k) =>
    endpointDiff_holder hF hw hH.hLeftDiff hH.comm hα0 hα1 (hTend K') i
  have hΛS0 : 0 ≤ ∑ J ∈ repWords k j', ΛS J := Finset.sum_nonneg fun J _ => (hΛS J).le
  have hΛT0 : 0 ≤ ∑ K' ∈ repWords k (j' + 1), ΛT K' := Finset.sum_nonneg fun K' _ => (hΛT K').le
  refine ⟨1 + (∑ J ∈ repWords k j', ΛS J) + ∑ K' ∈ repWords k (j' + 1), ΛT K', by linarith, ?_⟩
  intro v D Df K₀ hK₀ hKV hz hav hv hD hDf hrel
  -- the compact intrinsic class
  have hDI' : LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V I'.length α v D := by rw [hI']; exact hD
  have hweak : S.memWeakHolderX w C.Xl C.distanceGeometry.d F.V I'.length α v :=
    ⟨lt_top_iff_ne_top.2 hv, fun I'' hI'' =>
      ⟨D I'', (hDI' I'' hI'').1, lt_top_iff_ne_top.2 (hDI' I'' hI'').2⟩⟩
  have hmemX : memHolderX w C.Xl C.dl F.V I'.length α v :=
    S.memHolderX_of_memWeakHolderX C.chartOpens F.V C.distanceGeometry
      hF.lifted.subset_chartOpens w C.Xl hXt I'.length hα0 hweak
  have hsupp : closure ((F.V : Set (Fin (n + m) → ℝ)) ∩ Function.support v) ⊆ K₀ :=
    closure_minimal (fun x hx => by
      by_contra hxK
      exact hx.2 (hz x hx.1 hxK)) hK₀.isClosed
  have hvmemc : memHolderXCompact w C.Xl C.dl F.V I'.length α v :=
    ⟨hmemX, hK₀.of_isClosed_subset isClosed_closure hsupp, hsupp.trans hKV⟩
  obtain ⟨hid, -⟩ := hext α hα0 hα1 v hvmemc D hDI'
  have hfun : (fun x => a x * v x) = v := funext hav
  rw [hfun] at hid
  simp only [h1, h2] at hid
  -- jets
  have hD2 : IsWeakJet w C.Xl F.V (j' + 2) 2 v D := isWeakJet_of_holder hF.lifted hα0 hD
  have hwordS : ∀ J ∈ repWords k j', J ∈ wordFamily w (j' + 1) := fun J hJ => by
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
    have := mem_repWords.1 hJ
    omega
  have hz0 : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ K₀ → Df [] x = 0 := fun x hx hxK => by
    rw [← hrel x hx]
    have : weakSumSquares D [] x = ∑ i : Fin k, D ([] ++ [i, i]) x := rfl
    rw [this]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact jet_vanish_off hF.lifted hα0 hD hK₀.isClosed hz (K := [] ++ [i, i])
      (by rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]; simp) x hx hxK
  -- the inputs of the left-hand sums agree with the jet of `f`
  have hsumEq : ∀ J ∈ repWords k j', EqOn (weakSumSquares D J) (Df J)
      (F.V : Set (Fin (n + m) → ℝ)) := by
    intro J hJ
    have hJl : J.length + 2 ≤ j' + 2 := by
      have := mem_repWords.1 hJ
      omega
    have e1 := hD2.hasWeakWordDeriv_sumSquares hXt hw J hJl
    have e2 := repWeak_congr e1 (fun x hx => hrel x hx) (fun _ _ => rfl)
    have e3 := (hDf J (hwordS J hJ)).1
    have hc1 : ContinuousOn (weakSumSquares D J) (F.V : Set (Fin (n + m) → ℝ)) := by
      have : weakSumSquares D J = fun x => ∑ i : Fin k, D (J ++ [i, i]) x := rfl
      rw [this]
      refine continuousOn_finsetSum _ fun i _ => ?_
      refine LiftedChart.continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0
        (lt_top_iff_ne_top.2 (hD (J ++ [i, i]) ?_).2)
      rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hc2 : ContinuousOn (Df J) (F.V : Set (Fin (n + m) → ℝ)) :=
      LiftedChart.continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0
        (lt_top_iff_ne_top.2 (hDf J (hwordS J hJ)).2)
    exact eqOn_of_hasWeakWordDeriv_of_continuousOn e2 e3 hc1 hc2
  have hGeq : ∀ ξ, ((∑ J ∈ repWords k j', (Sf J).apply (weakSumSquares D J) ξ) +
      ∑ K' ∈ repWords k (j' + 1), (Tf K').apply (D K') ξ) =
      ((∑ J ∈ repWords k j', (Sf J).apply (Df J) ξ) +
        ∑ K' ∈ repWords k (j' + 1), (Tf K').apply (D K') ξ) := fun ξ => by
    have := hF.noAtoms
    congr 1
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [TypeOperator.apply_congr_of_eqOn_V (Sf J) (hsumEq J hJ)]
  -- sobolev data of the inputs
  have hSin : ∀ J ∈ repWords k j', memSobolevXZero w C.Xl F.V 1 2 (Df J) ∧
      IsWeakJet w C.Xl F.V 1 2 (Df J) (fun K' => Df (K' ++ J)) := fun J hJ =>
    jetEntry_sobolev hF.lifted hw hα0 (N := j') (u := Df []) hDf hK₀ hKV hz0 (K := J) (by
      rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
      have := mem_repWords.1 hJ
      omega)
  have hTin : ∀ K' ∈ repWords k (j' + 1), memSobolevXZero w C.Xl F.V 1 2 (D K') ∧
      IsWeakJet w C.Xl F.V 1 2 (D K') (fun K'' => D (K'' ++ K')) := fun K' hK' =>
    jetEntry_sobolev hF.lifted hw hα0 (N := j' + 1) (u := v) hD hK₀ hKV hz (K := K') (by
      rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
      have := mem_repWords.1 hK'
      omega)
  have hmemJ : ∀ J ∈ repWords k j', ∀ l : Fin k, [l] ++ J ∈ wordFamily w (j' + 1) := fun J hJ l => by
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
    have := mem_repWords.1 hJ
    simp only [List.singleton_append, List.length_cons]
    omega
  have hmemK : ∀ K' ∈ repWords k (j' + 1), ∀ l : Fin k, [l] ++ K' ∈ wordFamily w (j' + 2) :=
    fun K' hK' l => by
      rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
      have := mem_repWords.1 hK'
      simp only [List.singleton_append, List.length_cons]
      omega
  have hmemK0 : ∀ K' ∈ repWords k (j' + 1), K' ∈ wordFamily w (j' + 2) := fun K' hK' => by
    rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
    have := mem_repWords.1 hK'
    omega
  -- the differentiated identities
  have hS' := fun J (hJ : J ∈ repWords k j') =>
    hdS J (Df J) (fun K' => Df (K' ++ J)) (hSin J hJ).1 (hSin J hJ).2
      (hDf J (hwordS J hJ)).2
      (fun l => (hDf ([l] ++ J) (hmemJ J hJ l)).2)
  have hT' := fun K' (hK' : K' ∈ repWords k (j' + 1)) =>
    hdT K' (D K') (fun K'' => D (K'' ++ K')) (hTin K' hK').1 (hTin K' hK').2
      (hD K' (hmemK0 K' hK')).2 (fun l => (hD ([l] ++ K') (hmemK K' hK' l)).2)
  have hGder : hasWeakWordDeriv C.Xl F.V [i]
      (fun ξ => (∑ J ∈ repWords k j', (Sf J).apply (Df J) ξ) +
        ∑ K' ∈ repWords k (j' + 1), (Tf K').apply (D K') ξ)
      (fun ξ => (∑ J ∈ repWords k j', ∑ t, ((∑ l, (QS J t l).apply (Df ([l] ++ J)) ξ) +
          (QS0 J t).apply (Df J) ξ)) +
        ∑ K' ∈ repWords k (j' + 1), ∑ t, ((∑ l, (QT K' t l).apply (D ([l] ++ K')) ξ) +
          (QT0 K' t).apply (D K') ξ)) :=
    S.hasWeakWordDeriv_add C.Xl F.V hXt
      (repWeak_finset_sum hXt [i] _ _ _ fun J hJ => (hS' J hJ).1)
      (repWeak_finset_sum hXt [i] _ _ _ fun K' hK' => (hT' K' hK').1)
  have hid' : hasWeakWordDeriv C.Xl F.V I' v
      (fun ξ => (∑ J ∈ repWords k j', (Sf J).apply (Df J) ξ) +
        ∑ K' ∈ repWords k (j' + 1), (Tf K').apply (D K') ξ) :=
    repWeak_congr hid (fun _ _ => rfl) (fun ξ _ => hGeq ξ)
  refine ⟨_, (S.hasWeakWordDeriv_cons_iff C.Xl F.V hXt hid' i).mpr hGder, ?_, ?_⟩
  · exact (continuousOn_finsetSum _ fun J hJ => (hS' J hJ).2.1).add
      (continuousOn_finsetSum _ fun K' hK' => (hT' K' hK').2.1)
  · have hbS : ∀ J ∈ repWords k j', holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
        (fun ξ => ∑ t, ((∑ l, (QS J t l).apply (Df ([l] ++ J)) ξ) + (QS0 J t).apply (Df J) ξ)) ≤
        ENNReal.ofReal (ΛS J) *
          holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 1) Df := fun J hJ =>
      (hS' J hJ).2.2.trans (mul_le_mul' le_rfl
        (jetEntry_norm_le hw C.dl _ α (by have := mem_repWords.1 hJ; omega) Df))
    have hbT : ∀ K' ∈ repWords k (j' + 1), holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
        (fun ξ => ∑ t, ((∑ l, (QT K' t l).apply (D ([l] ++ K')) ξ) + (QT0 K' t).apply (D K') ξ)) ≤
        ENNReal.ofReal (ΛT K') *
          holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 2) D := fun K' hK' =>
      (hT' K' hK').2.2.trans (mul_le_mul' le_rfl
        (jetEntry_norm_le hw C.dl _ α (by have := mem_repWords.1 hK'; omega) D))
    refine (holderENorm_add_le hα0.le _ _).trans ?_
    refine (add_le_add
      (holderENorm_finsetSum_le_mul hα0.le (fun J ξ => ∑ t, ((∑ l, (QS J t l).apply (Df ([l] ++ J)) ξ) +
          (QS0 J t).apply (Df J) ξ)) ΛS (repWords k j') (fun J _ => (hΛS J).le) hbS)
      (holderENorm_finsetSum_le_mul hα0.le (fun K' ξ => ∑ t, ((∑ l, (QT K' t l).apply (D ([l] ++ K')) ξ) +
          (QT0 K' t).apply (D K') ξ)) ΛT (repWords k (j' + 1)) (fun K' _ => (hΛT K').le) hbT)).trans ?_
    exact ofReal_mul_add_le hΛS0 hΛT0 _ _

/-- **The compact recurrence with regularity** (BB (11.94), pp. 603-604, no drift).
For `j' ≥ 0` there is `Λ > 0` such that: if `v` is supported in a compact `K₀ ⊆ V` with `a v = v`, `v` has a
Hölder weak jet `D` of order `j' + 2`, and `Df` is a Hölder weak jet of order `j' + 1` of `f = Df []` with
`L̃ v = ∑ᵢ D [i, i] = f` on `V`, then `v` has a Hölder weak jet `D'` of order `j' + 3` extending `D`, and
`‖v‖_{C^{j'+3,α}(V)} ≤ Λ (‖f‖_{C^{j'+1,α}(V)} + ‖v‖_{C^{j'+2,α}(V)})` (in jet norms). -/
theorem compact_regularity (hH : HolderFrame C H K hQ F a) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (j' : ℕ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ (v : (Fin (n + m) → ℝ) → ℝ)
      (D Df : List (Fin k) → (Fin (n + m) → ℝ) → ℝ) (K₀ : Set (Fin (n + m) → ℝ)),
      IsCompact K₀ → K₀ ⊆ (F.V : Set (Fin (n + m) → ℝ)) →
      (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), x ∉ K₀ → v x = 0) → (∀ x, a x * v x = v x) →
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) v ≠ ⊤ →
      LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V (j' + 2) α v D →
      LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V (j' + 1) α (Df []) Df →
      (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), weakSumSquares D [] x = Df [] x) →
      ∃ D' : List (Fin k) → (Fin (n + m) → ℝ) → ℝ,
        LiftedChart.IsHolderWeakJet w C.Xl C.dl F.V (j' + 3) α v D' ∧
        (∀ K' : List (Fin k), K'.length ≤ j' + 2 → D' K' = D K') ∧
        holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 3) D' ≤ ENNReal.ofReal Λ *
          (holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 1) Df +
            holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 2) D) := by
  classical
  have hw := hH.weight
  choose! Λw hΛ using fun (I : List (Fin k)) (hI : I.length = j' + 3) =>
    exists_wordRegularity hH hα0 hα1 j' hI
  set W : Finset (List (Fin k)) := (wordFamily w (j' + 3)).filter (fun I => I.length = j' + 3)
    with hW
  have hΛ0 : 0 ≤ ∑ I ∈ W, Λw I := Finset.sum_nonneg fun I hI => ((hΛ I (Finset.mem_filter.1 hI).2).1).le
  refine ⟨1 + ∑ I ∈ W, Λw I, by linarith, ?_⟩
  intro v D Df K₀ hK₀ hKV hz hav hv hD hDf hrel
  set N : ℝ≥0∞ := holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 1) Df +
    holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 2) D with hN
  have hNtop : N ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun K' hK' => (hDf K' hK').2,
      ENNReal.sum_ne_top.2 fun K' hK' => (hD K' hK').2⟩
  have hg : ∀ I ∈ W, ∃ g : (Fin (n + m) → ℝ) → ℝ, hasWeakWordDeriv C.Xl F.V I v g ∧
      ContinuousOn g (F.V : Set (Fin (n + m) → ℝ)) ∧
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≤ ENNReal.ofReal (Λw I) * N := fun I hI =>
    (hΛ I (Finset.mem_filter.1 hI).2).2 v D Df K₀ hK₀ hKV hz hav hv hD hDf hrel
  choose! g hgw hgc hgb using hg
  refine ⟨fun K' => if K'.length ≤ j' + 2 then D K' else g K', ?_, fun K' hK' => by simp [hK'], ?_⟩
  · intro K' hK'
    have hlen : K'.length ≤ j' + 3 := by
      have := (S.mem_wordFamily_iff w (j' + 3) K').1 hK'
      rwa [wordWeight_eq_length hw] at this
    by_cases hc : K'.length ≤ j' + 2
    · have hK'' : K' ∈ wordFamily w (j' + 2) := by
        rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]; exact hc
      simp only [hc, ↓reduceIte]
      exact hD K' hK''
    · have hKW : K' ∈ W := Finset.mem_filter.2 ⟨hK', by omega⟩
      simp only [hc, ↓reduceIte]
      refine ⟨hgw K' hKW, ?_⟩
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNtop) (hgb K' hKW)
  · unfold holderJetNorm
    rw [← Finset.sum_filter_add_sum_filter_not (wordFamily w (j' + 3)) (fun K' => K'.length ≤ j' + 2)]
    have e1 : ∑ K' ∈ (wordFamily w (j' + 3)).filter (fun K' => K'.length ≤ j' + 2),
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
          ((fun K' => if K'.length ≤ j' + 2 then D K' else g K') K') ≤
        holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 2) D := by
      unfold holderJetNorm
      refine (Finset.sum_congr rfl fun K' hK' => ?_).trans_le (Finset.sum_le_sum_of_subset ?_)
      · simp only [(Finset.mem_filter.1 hK').2, ↓reduceIte]
      · intro K' hK'
        have := Finset.mem_filter.1 hK'
        rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
        exact this.2
    have e2 : ∑ K' ∈ (wordFamily w (j' + 3)).filter (fun K' => ¬ K'.length ≤ j' + 2),
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
          ((fun K' => if K'.length ≤ j' + 2 then D K' else g K') K') ≤
        ENNReal.ofReal (∑ I ∈ W, Λw I) * N := by
      have hsub : (wordFamily w (j' + 3)).filter (fun K' => ¬ K'.length ≤ j' + 2) ⊆ W := by
        intro K' hK'
        have h1 := Finset.mem_filter.1 hK'
        have hlen : K'.length ≤ j' + 3 := by
          have := (S.mem_wordFamily_iff w (j' + 3) K').1 h1.1
          rwa [wordWeight_eq_length hw] at this
        exact Finset.mem_filter.2 ⟨h1.1, by omega⟩
      calc _ = ∑ K' ∈ (wordFamily w (j' + 3)).filter (fun K' => ¬ K'.length ≤ j' + 2),
              holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (g K') :=
            Finset.sum_congr rfl fun K' hK' => by simp [(Finset.mem_filter.1 hK').2]
        _ ≤ ∑ K' ∈ W, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (g K') :=
            Finset.sum_le_sum_of_subset hsub
        _ ≤ ∑ K' ∈ W, ENNReal.ofReal (Λw K') * N := Finset.sum_le_sum fun K' hK' => hgb K' hK'
        _ = ENNReal.ofReal (∑ I ∈ W, Λw I) * N := by
            rw [ENNReal.ofReal_sum_of_nonneg fun I hI => ((hΛ I (Finset.mem_filter.1 hI).2).1).le,
              Finset.sum_mul]
    calc _ ≤ holderJetNorm w C.dl (F.V : Set (Fin (n + m) → ℝ)) α (j' + 2) D +
          ENNReal.ofReal (∑ I ∈ W, Λw I) * N := add_le_add e1 e2
      _ ≤ ENNReal.ofReal 1 * N + ENNReal.ofReal (∑ I ∈ W, Λw I) * N := by
          refine add_le_add ?_ le_rfl
          rw [ENNReal.ofReal_one, one_mul]
          exact le_add_self
      _ = ENNReal.ofReal (1 + ∑ I ∈ W, Λw I) * N := by
          rw [← add_mul, ENNReal.ofReal_add zero_le_one hΛ0]

end Frame

end RothschildStein.P2.HigherHolder

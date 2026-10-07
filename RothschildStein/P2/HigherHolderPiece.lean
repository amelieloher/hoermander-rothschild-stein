-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderStep

/-!
# The pieces of one step of the cutoff recurrence

Part of the higher Hölder estimate (BB p. 604). The lemmas used by `stage_step` (in `HigherHolderStepRoot`), each proved on its own:

* `jetConst`, `card_mul_eq`, `leibJet_norm_le`: the jet norm of a zero-extended Leibniz product
  (`holderJetNorm_leibJet_le` with the constant `|wordFamily N| 2^N`);
* `word_bound_field`, `holderJetNorm_forcingJet_le`: norms of the forcing jet from those of its three Leibniz parts;
* `leibJet_isHolderWeakJet`, `forcingJet_isHolderWeakJet`: the Hölder weak jets of the cutoff product and of the
  forcing term on the patch;
* `cutoff_deriv_facts`: smoothness and supports of the first two field derivatives of the cutoff;
* `stage_restrict`: restriction of a jet of the cutoff product to the ball where the cutoff is `1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

/-- The constant `|wordFamily_N| 2^N` of the Leibniz bound. -/
def jetConst (q N : ℕ) : ℝ := ((wordFamily (noDriftWeight : Fin q → ℕ+) N).card : ℝ) * 2 ^ N

theorem jetConst_nonneg (q N : ℕ) : 0 ≤ jetConst q N := by
  unfold jetConst
  positivity

theorem card_mul_eq {q : ℕ} (N : ℕ) (c : ℝ) :
    ((wordFamily (noDriftWeight : Fin q → ℕ+) N).card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ N * ENNReal.ofReal c) =
      ENNReal.ofReal (jetConst q N) * ENNReal.ofReal c := by
  unfold jetConst
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]
  ring

section Generic

variable {n' q : ℕ} {X : Fin q → (Fin n' → ℝ) → (Fin n' → ℝ)}

/-- A uniform bound for the words of length at most `N` passes to the derivatives of the cutoff. -/
theorem word_bound_field {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} {B : Set (Fin n' → ℝ)}
    {ζ : (Fin n' → ℝ) → ℝ} {N : ℕ} {c : ℝ}
    (h : ∀ J : List (Fin q), J.length ≤ N → holderENorm d α B (wordDerivative X J ζ) ≤ ENNReal.ofReal c)
    (τ J : List (Fin q)) (hJ : J.length + τ.length ≤ N) :
    holderENorm d α B (wordDerivative X J (wordDerivative X τ ζ)) ≤ ENNReal.ofReal c := by
  rw [← wordDerivative_append_apply J τ ζ]
  refine h _ ?_
  rw [List.length_append]
  exact hJ

/-- The jet norm of the forcing jet is at most `(1 + 3 q) M` when the three Leibniz parts are at most `M`. -/
theorem holderJetNorm_forcingJet_le {w : Fin q → ℕ+} (d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞)
    (V B : Set (Fin n' → ℝ)) {α : ℝ} (hα : 0 ≤ α) (N : ℕ) (ζ : (Fin n' → ℝ) → ℝ)
    (Du Df : List (Fin q) → (Fin n' → ℝ) → ℝ) {M : ℝ≥0∞}
    (h1 : holderJetNorm w d V α N (leibJet X B ζ Df) ≤ M)
    (h2 : ∀ i : Fin q, holderJetNorm w d V α N
      (leibJet X B (fieldDerivative (X i) ζ) (fun K'' => Du (K'' ++ [i]))) ≤ M)
    (h3 : ∀ i : Fin q, holderJetNorm w d V α N
      (leibJet X B (fieldDerivative (X i) (fieldDerivative (X i) ζ)) Du) ≤ M) :
    holderJetNorm w d V α N (forcingJet X B ζ Du Df) ≤ M * (1 + 3 * (q : ℝ≥0∞)) := by
  classical
  have hle : holderJetNorm w d V α N (forcingJet X B ζ Du Df) ≤
      holderJetNorm w d V α N (leibJet X B ζ Df) +
        ∑ i : Fin q, (holderJetNorm w d V α N
            (leibJet X B (fieldDerivative (X i) ζ) (fun K'' => Du (K'' ++ [i]))) +
          holderJetNorm w d V α N
            (leibJet X B (fieldDerivative (X i) ζ) (fun K'' => Du (K'' ++ [i]))) +
          holderJetNorm w d V α N
            (leibJet X B (fieldDerivative (X i) (fieldDerivative (X i) ζ)) Du)) := by
    unfold holderJetNorm
    refine (Finset.sum_le_sum fun K' _ => holderENorm_forcingJet_le hα V B ζ Du Df K').trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_add_distrib]
  refine hle.trans ?_
  calc _ ≤ M + ∑ i : Fin q, (M + M + M) :=
        add_le_add h1 (Finset.sum_le_sum fun i _ => add_le_add (add_le_add (h2 i) (h2 i)) (h3 i))
    _ = M * (1 + 3 * (q : ℝ≥0∞)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Generic

section Piece

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m}

/-- **The jet norm of a zero-extended Leibniz product** (zero extension by a first-exit argument, and the weak product rule):
`‖(D ζ)‖_{N, C^α(V)} ≤ |wordFamily N| 2^N c ‖D‖_{N, C^α(B)}` when `tsupport ζ ⊆ B ⊆ V` is compact in `B`
and `‖X̃_J ζ‖_{C^α(B)} ≤ c` for `|J| ≤ N`. -/
theorem leibJet_norm_le {V B : Opens (Fin (n + m) → ℝ)} (hBV : (B : Set (Fin (n + m) → ℝ)) ⊆ V)
    (hBU : (B : Set (Fin (n + m) → ℝ)) ⊆ C.U) {α : ℝ} (hα0 : 0 < α) {ζ : (Fin (n + m) → ℝ) → ℝ}
    {K₀ : Set (Fin (n + m) → ℝ)} (hK₀ : IsCompact K₀) (hK₀B : K₀ ⊆ (B : Set (Fin (n + m) → ℝ)))
    (htζ : tsupport ζ ⊆ K₀) {N : ℕ} {c : ℝ} {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hD : ∀ J ∈ wordFamily noDriftWeight N, holderENorm C.dl α (B : Set (Fin (n + m) → ℝ)) (D J) ≠ ⊤)
    (hζ : ∀ J : List (Fin q), J.length ≤ N →
      holderENorm C.dl α (B : Set (Fin (n + m) → ℝ)) (wordDerivative C.Xl J ζ) ≤ ENNReal.ofReal c) :
    holderJetNorm noDriftWeight C.dl (V : Set (Fin (n + m) → ℝ)) α N (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D) ≤
      ENNReal.ofReal (jetConst q N) * ENNReal.ofReal c *
        holderJetNorm noDriftWeight C.dl (B : Set (Fin (n + m) → ℝ)) α N D := by
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := fun j => noDriftWeight_coe_eq_one j
  have hw2 : ∀ i : Fin q, ((noDriftWeight i : ℕ+) : ℕ) ≤ 2 := fun i => by rw [hw i]; norm_num
  have hsB : ∀ x ∈ (B : Set (Fin (n + m) → ℝ)), ∀ y ∈ (B : Set (Fin (n + m) → ℝ)),
      controlDistance C.O noDriftWeight C.Xl x y = 0 → x = y := fun x hx y hy hd =>
    congrArg Subtype.val ((C.distanceGeometry.distance_eq_zero_iff ⟨x, hBU hx⟩ ⟨y, hBU hy⟩).mp hd)
  have h := holderJetNorm_leibJet_le (Ω₀ := C.O) (w := noDriftWeight) (X := C.Xl) hw2 hw hα0
    (V := (V : Set (Fin (n + m) → ℝ))) hBV B.isOpen hK₀ hK₀B htζ hsB (N := N) (c := c) (D := D) hD
    (fun J hJ => hζ J ((mem_wordFamily_iff_length hw).1 hJ))
  refine h.trans (le_of_eq ?_)
  rw [card_mul_eq]

/-- The Hölder weak jet on `V` of the zero-extended cutoff product. -/
theorem leibJet_isHolderWeakJet {V B : Opens (Fin (n + m) → ℝ)} (hBV : (B : Set (Fin (n + m) → ℝ)) ⊆ V)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {ζ : (Fin (n + m) → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hKc : IsCompact (tsupport ζ))
    (hKB : tsupport ζ ⊆ (B : Set (Fin (n + m) → ℝ))) {α : ℝ} {N : ℕ}
    {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hD : ∀ K' ∈ wordFamily noDriftWeight N, hasWeakWordDeriv C.Xl B K' (D []) (D K'))
    (hfin : holderJetNorm noDriftWeight C.dl (V : Set (Fin (n + m) → ℝ)) α N
      (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D) ≠ ⊤) :
    LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl V N α
      (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D []) (leibJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D) := by
  intro K' hK'
  refine ⟨?_, ne_top_of_le_ne_top hfin (single_le_holderJetNorm hK')⟩
  rw [leibJet_nil]
  exact hasWeakWordDeriv_leibJet (V := V) (B := B) hBV hX hζ hKc hKB
    (fun z hz => image_eq_zero_of_notMem_tsupport hz) (D := D) K'
    (fun J hJ => hD J (S.sublist_mem_wordFamily _ N hJ hK'))

/-- The Hölder weak jet on `V` of the forcing term `L̃ (ζ u)`. -/
theorem forcingJet_isHolderWeakJet {V B : Opens (Fin (n + m) → ℝ)} (hBV : (B : Set (Fin (n + m) → ℝ)) ⊆ V)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {ζ : (Fin (n + m) → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ1 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) ζ))
    (hζ2 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) ζ)))
    (hKc : IsCompact (tsupport ζ)) (hKB : tsupport ζ ⊆ (B : Set (Fin (n + m) → ℝ)))
    (hζ10 : ∀ i z, z ∉ tsupport ζ → fieldDerivative (C.Xl i) ζ z = 0)
    (hζ20 : ∀ i z, z ∉ tsupport ζ → fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) ζ) z = 0)
    {α : ℝ} {N : ℕ} {D Df : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hD : ∀ K' ∈ wordFamily noDriftWeight (N + 1), hasWeakWordDeriv C.Xl B K' (D []) (D K'))
    (hDf : ∀ K' ∈ wordFamily noDriftWeight N, hasWeakWordDeriv C.Xl B K' (Df []) (Df K'))
    (hfin : holderJetNorm noDriftWeight C.dl (V : Set (Fin (n + m) → ℝ)) α N
      (forcingJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D Df) ≠ ⊤) :
    LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl V N α
      (forcingJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D Df [])
      (forcingJet C.Xl (B : Set (Fin (n + m) → ℝ)) ζ D Df) := by
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := fun j => noDriftWeight_coe_eq_one j
  have hXB : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (B : Set (Fin (n + m) → ℝ)) := fun i =>
    (hX i).mono hBV
  intro K' hK'
  refine ⟨?_, ne_top_of_le_ne_top hfin (single_le_holderJetNorm hK')⟩
  have hK'2 : K' ∈ wordFamily noDriftWeight (N + 1) := by
    rw [mem_wordFamily_iff_length hw] at hK' ⊢
    omega
  exact hasWeakWordDeriv_forcingJet (V := V) (B := B) hBV hX hζ hζ1 hζ2 hKc hKB
    (fun z hz => image_eq_zero_of_notMem_tsupport hz) hζ10 hζ20 K'
    (fun J hJ => hD J (S.sublist_mem_wordFamily _ (N + 1) hJ hK'2))
    (fun i J hJ => jet_append hXB hD [i] J (by
      have h1 := (mem_wordFamily_iff_length hw).1 hK'
      have h2 := hJ.length_le
      rw [mem_wordFamily_iff_length hw]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega))
    (fun J hJ => hDf J (S.sublist_mem_wordFamily _ N hJ hK'))

/-- Smoothness and supports of the first two field derivatives of the cutoff. -/
theorem cutoff_deriv_facts {ζ : (Fin (n + m) → ℝ) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hU : tsupport ζ ⊆ C.U) :
    (∀ i, tsupport (fieldDerivative (C.Xl i) ζ) ⊆ tsupport ζ) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) ζ)) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) ζ))) ∧
      (∀ i z, z ∉ tsupport ζ → fieldDerivative (C.Xl i) ζ z = 0) ∧
      (∀ i z, z ∉ tsupport ζ → fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) ζ) z = 0) := by
  have hs1 : ∀ i, tsupport (fieldDerivative (C.Xl i) ζ) ⊆ tsupport ζ := fun i =>
    S.tsupport_fieldDerivative_subset _ _
  have h1 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) ζ) := fun i =>
    LiftedChart.contDiff_fieldDerivative_Xl_noDrift hζ hU i
  refine ⟨hs1, h1, fun i => LiftedChart.contDiff_fieldDerivative_Xl_noDrift (h1 i) ((hs1 i).trans hU) i,
    fun i z hz => image_eq_zero_of_notMem_tsupport (fun h => hz (hs1 i h)), fun i z hz => ?_⟩
  exact image_eq_zero_of_notMem_tsupport (fun h =>
    hz ((S.tsupport_fieldDerivative_subset _ _).trans (hs1 i) h))

/-- **Restriction to the ball where the cutoff is `1`**: a Hölder weak jet `D'` of order `j' + 3` of
`v` on `V`, with `v = D []` on `Bs ⊆ B ⊆ V`, restricts to a Hölder weak jet of `D' [] = v` on `Bs`, and `D' = D`
on `Bs` for the words of length at most `j' + 2` (uniqueness of continuous weak derivatives). -/
theorem stage_restrict {V B Bs : Opens (Fin (n + m) → ℝ)} (hBsB : (Bs : Set (Fin (n + m) → ℝ)) ⊆ B)
    (hBV : (B : Set (Fin (n + m) → ℝ)) ⊆ V) (hBsU : (Bs : Set (Fin (n + m) → ℝ)) ⊆ C.U) {α : ℝ}
    (hα0 : 0 < α) {j' : ℕ} {v : (Fin (n + m) → ℝ) → ℝ} {D D' : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hvD : ∀ x ∈ (Bs : Set (Fin (n + m) → ℝ)), v x = D [] x)
    (hD'J : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl V (j' + 3) α v D')
    (hD'nil : D' [] = v)
    (hDw : ∀ K' ∈ wordFamily noDriftWeight (j' + 2), hasWeakWordDeriv C.Xl B K' (D []) (D K'))
    (hDfin : ∀ K' ∈ wordFamily noDriftWeight (j' + 2),
      holderENorm C.dl α (B : Set (Fin (n + m) → ℝ)) (D K') ≠ ⊤) :
    LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl Bs (j' + 3) α (D' []) D' ∧
      ∀ K' : List (Fin q), K'.length ≤ j' + 2 →
        ∀ x ∈ (Bs : Set (Fin (n + m) → ℝ)), D' K' x = D K' x := by
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := fun j => noDriftWeight_coe_eq_one j
  have hBsV : (Bs : Set (Fin (n + m) → ℝ)) ⊆ V := hBsB.trans hBV
  have hD'weak : ∀ K' ∈ wordFamily noDriftWeight (j' + 3),
      hasWeakWordDeriv C.Xl Bs K' v (D' K') := fun K' hK' =>
    S.hasWeakWordDeriv_restrict C.Xl V Bs hBsV (hD'J K' hK').1
  have hD'fin : ∀ K' ∈ wordFamily noDriftWeight (j' + 3),
      holderENorm C.dl α (Bs : Set (Fin (n + m) → ℝ)) (D' K') ≠ ⊤ := fun K' hK' =>
    ne_top_of_le_ne_top (hD'J K' hK').2 (S.holderENorm_mono C.dl α _ _ hBsV)
  refine ⟨fun K' hK' => ⟨?_, hD'fin K' hK'⟩, ?_⟩
  · rw [hD'nil]
    exact hD'weak K' hK'
  · intro K' hK' x hx
    have hK'2 : K' ∈ wordFamily noDriftWeight (j' + 2) := (mem_wordFamily_iff_length hw).2 hK'
    have hK'3 : K' ∈ wordFamily noDriftWeight (j' + 3) := by
      rw [mem_wordFamily_iff_length hw] at hK'2 ⊢
      omega
    have h2 : hasWeakWordDeriv C.Xl Bs K' v (D K') := by
      refine S.hasWeakWordDeriv_congr_ae C.Xl Bs (S.hasWeakWordDeriv_restrict C.Xl B Bs hBsB
        (hDw K' hK'2)) ?_ Filter.EventuallyEq.rfl
      rw [Filter.EventuallyEq, ae_restrict_iff' Bs.isOpen.measurableSet]
      exact Filter.Eventually.of_forall fun y hy => (hvD y hy).symm
    have hc1 : ContinuousOn (D' K') (Bs : Set (Fin (n + m) → ℝ)) :=
      LiftedChart.continuousOn_of_holderENorm_lt_top hBsU hα0 (lt_top_iff_ne_top.2 (hD'fin K' hK'3))
    have hc2 : ContinuousOn (D K') (Bs : Set (Fin (n + m) → ℝ)) :=
      LiftedChart.continuousOn_of_holderENorm_lt_top hBsU hα0 (lt_top_iff_ne_top.2
        (ne_top_of_le_ne_top (hDfin K' hK'2) (S.holderENorm_mono C.dl α _ _ hBsB)))
    exact eqOn_of_hasWeakWordDeriv_of_continuousOn (hD'weak K' hK'3) h2 hc1 hc2 hx

end Piece

end RothschildStein.P2.HigherHolder

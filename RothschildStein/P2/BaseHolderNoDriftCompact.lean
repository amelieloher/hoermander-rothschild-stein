-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderNoDriftJet
public import RothschildStein.P1.WeakExtensionNoDriftMain
public import RothschildStein.P1.ContinuityTheorem
public import RothschildStein.P1.KernelEstimatesChart

/-!
# No drift: the compact `C^{2,α}` estimate (BB (11.61))

Part of the base Hölder estimate. BB state the compact estimate (11.61) (p. 577, Thm 11.34) and use it
at p. 601 for `ζ u` without a proof in this form; it is proved here. For `v` in the
compact intrinsic class `C^{2,α}_{X̃,0}(V)` of the patch `V = F.V` of a standard frame with `a v = v` (`a` the
cutoff of the first- and second-order representations) and Hölder weak jet `D` (alphabet `Fin q`, all weights one,
`L̃ v = ∑ᵢ D [i, i]`):

* `HolderFromSupNoDrift` (`exists_holderFromSup_noDrift_of_representation`): the parametrix identity
  `v = P₂ L̃v + F₂ v` (extended to compact `C^{2,α}` inputs by the weak extension theorem) and the first
  Hölder interpolation inequality give `‖v‖_{C^α} ≤ C₃ (‖L̃v‖_∞ + ‖v‖_∞)`;
* `CompactHolderEstimateNoDrift` (`exists_compactHolder_noDrift_of_representation`): the second-order
  representation `X̃ᵢX̃ₗ v = S_{il} L̃v + ∑ₖ S_{ilk} X̃ₖ v + S_{il0} v`, the Hölder bound of the type-0
  operators (the continuity theorem), and the derivative Hölder interpolation inequality give `‖v‖_{C^{2,α}} ≤ Λ (‖L̃v‖_{C^α} + ‖v‖_∞)`.

Both assume exactly the hypotheses of the first- and second-order representations without drift
(`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, the `SignedParametrixNoDrift`s with the density data) and
a standard frame; the `(HD)` package is that of the lifted chart (`LiftedChart.distanceGeometry`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Helpers

variable {N : ℕ}

/-- The Hölder norm of a finite sum is at most the sum of the norms. -/
theorem holderENorm_finset_sum_le {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α)
    {V : Set (Fin N → ℝ)} {ι : Type*} (s : Finset ι) (f : ι → (Fin N → ℝ) → ℝ) :
    holderENorm d α V (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, holderENorm d α V (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun x => ∑ i ∈ (∅ : Finset ι), f i x) = fun _ => (0 : ℝ) := by
      funext x
      simp
    rw [this, holderENorm_zero]
    simp
  | insert a s ha ih =>
    have e : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x
      rw [Finset.sum_insert ha]
    rw [e, Finset.sum_insert ha]
    exact (holderENorm_add_le hα _ _).trans (add_le_add le_rfl ih)

/-- A finite family of reals has a nonnegative common upper bound. -/
theorem exists_common_upper_bound {ι : Type*} [Finite ι] (f : ι → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, f i ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨max M 0, le_max_right _ _, fun i => (hM ⟨i, rfl⟩).trans (le_max_left _ _)⟩

end Helpers

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- No drift: the Hölder norm of a compactly supported `v` is controlled by sup
norms (`‖v‖_{C^α(V)} ≤ C₃ (‖L̃v‖_∞ + ‖v‖_∞)`). -/
def HolderFromSupNoDrift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (a : TestFunction F.V ℝ (⊤ : ℕ∞)) (α C₃ : ℝ) : Prop :=
  ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
    memHolderXCompact noDriftWeight C.Xl C.dl F.V 2 α v →
    LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α v D → (∀ x, a x * v x = v x) →
    holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) v ≤
      ENNReal.ofReal C₃ * (supNormE (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D []) +
        supNormE (F.V : Set (Fin (n + m) → ℝ)) v)

/-- **The compact `C^{2,α}` estimate (BB (11.61))** in sup form, no drift:
`‖v‖_{C^{2,α}(V)} ≤ Λ (‖L̃v‖_{C^α(V)} + ‖v‖_{L^∞(V)})`, the left side computed on the Hölder weak jet
(`jetENormNoDrift`; equal to `holderXENorm` by `holderXENorm_eq_jetENormNoDrift`). -/
def CompactHolderEstimateNoDrift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    (F : KernelFrame (n + m)) (a : TestFunction F.V ℝ (⊤ : ℕ∞)) (α Λ : ℝ) : Prop :=
  ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
    memHolderXCompact noDriftWeight C.Xl C.dl F.V 2 α v →
    LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α v D → (∀ x, a x * v x = v x) →
    jetENormNoDrift C.dl α (F.V : Set (Fin (n + m) → ℝ)) D ≤
      ENNReal.ofReal Λ * (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D []) +
        supNormE (F.V : Set (Fin (n + m) → ℝ)) v)

variable {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **Hölder norm from sup norms for compactly supported `C^{2,α}`, no drift.**
Under the hypotheses of the derivative representations on a standard frame there is `C₃` with
`‖v‖_{C^α(V)} ≤ C₃ (‖L̃v‖_∞ + ‖v‖_∞)` for every compactly supported intrinsic `C^{2,α}_{X̃}` function `v` of the
patch with `a v = v` (left identity `v = P₂ L̃v + F₂ v`, first interpolation inequality with `ε = 1/2`,
`L^∞ → C^α` bound of the type-one operator `F₂`). -/
theorem exists_holderFromSup_noDrift_of_representation (hF : C.IsStandardFrame F H K hQ)
    (hLeftDiff : LeftDifferentiation F noDriftWeight C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ HolderFromSupNoDrift C F a α C₃ := by
  classical
  obtain ⟨P₂, F₂, Fl, Sl, -, hid⟩ := exists_compactIdentities_noDrift_of_representation hF hLeftDiff hc hc0
    a hParametrix hα0 hα1
  obtain ⟨γ₂, C₂, hγ₂, hC₂, hA₂⟩ := exists_fractional_interpolation_holder_noDrift C hF.lifted
    (lam := 2) (by norm_num) P₂ hα0 hα1
  obtain ⟨CH₂, hCH₂, hF₂b⟩ := TypeOperator.exists_holderENorm_bound hF.lifted (le_refl 1) F₂ hα0 hα1
  have hc' : 0 ≤ C₂ * (1 / 2 : ℝ) ^ (-γ₂) + CH₂ :=
    add_nonneg (mul_nonneg hC₂.le (Real.rpow_nonneg (by norm_num) _)) hCH₂.le
  refine ⟨1 / 2 + (C₂ * (1 / 2 : ℝ) ^ (-γ₂) + CH₂), by positivity, fun v D hv hD hav => ?_⟩
  obtain ⟨hleft, -⟩ := hid v D hv hD hav
  have hvc : ContinuousOn v (F.V : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0 hv.1.1
  have hvm : AEStronglyMeasurable v (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
    hvc.aestronglyMeasurable F.V.isOpen.measurableSet
  have h1 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) v ≤
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun ξ => P₂.apply (weakSumSquares D []) ξ) +
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (F₂.apply v) := by
    calc _ = holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
          (fun ξ => P₂.apply (weakSumSquares D []) ξ + F₂.apply v ξ) :=
          S.holderENorm_congr C.dl α (F.V : Set (Fin (n + m) → ℝ)) v hleft
      _ ≤ _ := holderENorm_add_le hα0.le _ _
  have h2 := hA₂ (1 / 2) one_half_pos (by norm_num) v D hv hD
  have h3 := hF₂b v hvm
  change _ ≤ ENNReal.ofReal (1 / 2) * supNormE (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D []) +
    ENNReal.ofReal (C₂ * (1 / 2 : ℝ) ^ (-γ₂)) * supNormE (F.V : Set (Fin (n + m) → ℝ)) v at h2
  change _ ≤ ENNReal.ofReal CH₂ * supNormE (F.V : Set (Fin (n + m) → ℝ)) v at h3
  set S1 := supNormE (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D [])
  set S2 := supNormE (F.V : Set (Fin (n + m) → ℝ)) v
  have b1 : BoundedBy (ENNReal.ofReal (1 / 2) * S1) (S1 + S2) (1 / 2) :=
    BoundedBy.of_const_mul_le (by norm_num) le_self_add
  have b2 : BoundedBy (ENNReal.ofReal (C₂ * (1 / 2 : ℝ) ^ (-γ₂)) * S2 + ENNReal.ofReal CH₂ * S2)
      (S1 + S2) (C₂ * (1 / 2 : ℝ) ^ (-γ₂) + CH₂) := by
    have e : ENNReal.ofReal (C₂ * (1 / 2 : ℝ) ^ (-γ₂)) * S2 + ENNReal.ofReal CH₂ * S2 =
        ENNReal.ofReal (C₂ * (1 / 2 : ℝ) ^ (-γ₂) + CH₂) * S2 := by
      rw [← add_mul, ENNReal.ofReal_add (mul_nonneg hC₂.le (Real.rpow_nonneg (by norm_num) _))
        hCH₂.le]
    rw [e]
    exact BoundedBy.of_const_mul_le hc' le_add_self
  have := (b1.add b2 (by norm_num) hc')
  unfold BoundedBy at this
  calc _ ≤ _ := h1
    _ ≤ (ENNReal.ofReal (1 / 2) * S1 + ENNReal.ofReal (C₂ * (1 / 2 : ℝ) ^ (-γ₂)) * S2) +
        ENNReal.ofReal CH₂ * S2 := add_le_add h2 h3
    _ = ENNReal.ofReal (1 / 2) * S1 + (ENNReal.ofReal (C₂ * (1 / 2 : ℝ) ^ (-γ₂)) * S2 +
        ENNReal.ofReal CH₂ * S2) := by rw [add_assoc]
    _ ≤ _ := this

/-- **The compact `C^{2,α}` estimate (BB p. 577, (11.61)), no drift.** Under the
hypotheses of the derivative representations (`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, the
`SignedParametrixNoDrift`s with the density data) on a standard frame and `0 < α < 1` there is `Λ` such that for every
compactly supported intrinsic `C^{2,α}_{X̃}` function `v` of the patch `V = F.V` with Hölder weak jet `D` and
`a v = v`, `‖v‖_{C^{2,α}(V)} ≤ Λ (‖L̃v‖_{C^α(V)} + ‖v‖_{L^∞(V)})`.
Proof: the second-order representation `X̃ᵢX̃ₗ v = S_{il} L̃v + ∑ₖ S_{ilk} X̃ₖ v + S_{il0} v` pointwise (a continuous weak derivative is the
continuous representative), the Hölder bound of the type-0 operators (the continuity theorem), the derivative interpolation
`∑ₗ ‖X̃ₗ v‖_{C^α} ≤ ½ ‖L̃v‖_∞ + C ‖v‖_∞` of the Hölder interpolation inequalities and `‖v‖_{C^α} ≤ C₃ (‖L̃v‖_∞ + ‖v‖_∞)`
(`exists_holderFromSup_noDrift_of_representation`). -/
theorem exists_compactHolder_noDrift_of_representation (hF : C.IsStandardFrame F H K hQ)
    (B : Fin (n + m) → List (Fin q)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F noDriftWeight C.Xl)
    (hRightDiff : RightDifferentiation F noDriftWeight C.Xl hF.lifted.contDiffOn_Xl)
    (hTransfer : DerivativeTransfer F noDriftWeight C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ Λ : ℝ, 0 < Λ ∧ CompactHolderEstimateNoDrift C F a α Λ := by
  classical
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := noDriftWeight_natCast_eq_one
  obtain ⟨C₃, hC₃, hsupH⟩ := exists_holderFromSup_noDrift_of_representation hF hLeftDiff hc hc0 a hParametrix hα0
    hα1
  obtain ⟨γ, Cc, hγ, hCc, hder⟩ := exists_derivativeInterpolation_noDrift_of_representation hF hLeftDiff
    hc hc0 a hParametrix hα0 hα1
  obtain ⟨Sml, Smlk, Sml0, -, -, -, -, -, -, hext⟩ :=
    LiftedChart.weakExtension_secondOrder_full_noDrift_of hF hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
  choose CH1 hCH1 hV1 hb1 using fun i l : Fin q =>
    (Sml i l).exists_holderENorm_bound_standard hF hα0 hα1
  choose CH2 hCH2 hV2 hb2 using fun i l k : Fin q =>
    (Smlk i l k).exists_holderENorm_bound_standard hF hα0 hα1
  choose CH3 hCH3 hV3 hb3 using fun i l : Fin q =>
    (Sml0 i l).exists_holderENorm_bound_standard hF hα0 hα1
  obtain ⟨M1, hM10, hM1⟩ := exists_common_upper_bound (fun p : Fin q × Fin q => CH1 p.1 p.2)
  obtain ⟨M2, hM20, hM2⟩ :=
    exists_common_upper_bound (fun p : Fin q × Fin q × Fin q => CH2 p.1 p.2.1 p.2.2)
  obtain ⟨M3, hM30, hM3⟩ := exists_common_upper_bound (fun p : Fin q × Fin q => CH3 p.1 p.2)
  set cE : ℝ := 1 / 2 + Cc * (1 / 2 : ℝ) ^ (-γ) with hcE
  have hcE0 : 0 ≤ cE :=
    add_nonneg (by norm_num) (mul_nonneg hCc.le (Real.rpow_nonneg (by norm_num) _))
  set cP : ℝ := M1 + M2 * cE + M3 * C₃ with hcP
  have hcP0 : 0 ≤ cP := by
    have : 0 ≤ M2 * cE := mul_nonneg hM20 hcE0
    have : 0 ≤ M3 * C₃ := mul_nonneg hM30 hC₃.le
    linarith
  have hqq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine ⟨C₃ + cE + q * (q * cP) + 1, by positivity, fun v D hv hD hav => ?_⟩
  set V : Set (Fin (n + m) → ℝ) := (F.V : Set (Fin (n + m) → ℝ)) with hV
  set Ef := holderENorm C.dl α V (weakSumSquares D []) with hEf
  set Sv := supNormE V v with hSv
  set Y := Ef + Sv with hY
  have hvc : ContinuousOn v V :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0 hv.1.1
  have hSg : supNormE V (weakSumSquares D []) ≤ Ef := supNormE_le_holderENorm _ _
  have hEfY : Ef ≤ Y := le_self_add
  have hSvY : Sv ≤ Y := le_add_self
  -- the Hölder norm of `v`
  have bv : BoundedBy (holderENorm C.dl α V v) Y C₃ :=
    (hsupH v D hv hD hav).trans (mul_le_mul' le_rfl (add_le_add hSg le_rfl))
  -- the first derivatives
  have bE1 : BoundedBy (∑ k : Fin q, holderENorm C.dl α V (D [k])) Y cE := by
    have h := hder (1 / 2) one_half_pos (by norm_num) v D hv hD hav
    change _ ≤ ENNReal.ofReal (1 / 2) * supNormE V (weakSumSquares D []) +
      ENNReal.ofReal (Cc * (1 / 2 : ℝ) ^ (-γ)) * supNormE V v at h
    have b1 : BoundedBy (ENNReal.ofReal (1 / 2) * supNormE V (weakSumSquares D [])) Y (1 / 2) :=
      BoundedBy.of_const_mul_le (by norm_num) (hSg.trans hEfY)
    have b2 : BoundedBy (ENNReal.ofReal (Cc * (1 / 2 : ℝ) ^ (-γ)) * Sv) Y
        (Cc * (1 / 2 : ℝ) ^ (-γ)) :=
      BoundedBy.of_const_mul_le (mul_nonneg hCc.le (Real.rpow_nonneg (by norm_num) _)) hSvY
    exact (b1.add b2 (by norm_num) (mul_nonneg hCc.le (Real.rpow_nonneg (by norm_num) _))).mono_left h
  have hLfin : holderENorm C.dl α V (weakSumSquares D []) ≠ ⊤ :=
    hD.weakSumSquares_nil_ne_top hw hα0
  have hvfin : holderENorm C.dl α V v ≠ ⊤ := ne_top_of_lt hv.1.1
  have hDk : ∀ k : Fin q, holderENorm C.dl α V (D [k]) ≠ ⊤ := fun k =>
    (hD _ (LiftedChart.horizontal_mem_wordFamily_noDrift hw k)).2
  -- the second derivatives
  have bpair : ∀ i l : Fin q, BoundedBy (holderENorm C.dl α V (D [i, l])) Y cP := by
    intro i l
    obtain ⟨hweak, hcont⟩ := hext α hα0 hα1 v hv D hD i l
    have hav' : (fun x => a x * v x) = v := funext hav
    rw [hav'] at hweak
    have hmem : [i, l] ∈ wordFamily noDriftWeight 2 :=
      (S.mem_wordFamily_iff _ _ _).2 (by simp [wordWeight, noDriftWeight])
    obtain ⟨hDw, hDf⟩ := hD _ hmem
    have hDc := LiftedChart.continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0
      (lt_top_iff_ne_top.2 hDf)
    have heq := eqOn_of_hasWeakWordDeriv_of_continuousOn hDw hweak hDc hcont
    rw [S.holderENorm_congr C.dl α V _ heq]
    have h1 := holderENorm_add_le (d := C.dl) (α := α) (V := V) hα0.le
      (fun ξ => (Sml i l).apply (weakSumSquares D []) ξ +
        ∑ k : Fin q, (Smlk i l k).apply (D [k]) ξ) (fun ξ => (Sml0 i l).apply v ξ)
    have h2 := holderENorm_add_le (d := C.dl) (α := α) (V := V) hα0.le
      (fun ξ => (Sml i l).apply (weakSumSquares D []) ξ)
      (fun ξ => ∑ k : Fin q, (Smlk i l k).apply (D [k]) ξ)
    have h3 := holderENorm_finset_sum_le (d := C.dl) (α := α) (V := V) hα0.le
      (Finset.univ : Finset (Fin q)) (fun k ξ => (Smlk i l k).apply (D [k]) ξ)
    have t1 : holderENorm C.dl α V (fun ξ => (Sml i l).apply (weakSumSquares D []) ξ) ≤
        ENNReal.ofReal (CH1 i l) * Ef := hb1 i l _
    have t2 : ∀ k : Fin q, holderENorm C.dl α V (fun ξ => (Smlk i l k).apply (D [k]) ξ) ≤
        ENNReal.ofReal (CH2 i l k) * holderENorm C.dl α V (D [k]) := fun k => hb2 i l k _
    have t3 : holderENorm C.dl α V (fun ξ => (Sml0 i l).apply v ξ) ≤
        ENNReal.ofReal (CH3 i l) * holderENorm C.dl α V v := hb3 i l _
    have bt1 : BoundedBy (ENNReal.ofReal (CH1 i l) * Ef) Y M1 :=
      (BoundedBy.of_const_mul_le (hCH1 i l).le hEfY).mono (hM1 (i, l))
    have bt2 : BoundedBy (∑ k : Fin q, ENNReal.ofReal (CH2 i l k) * holderENorm C.dl α V (D [k]))
        Y (M2 * cE) := by
      have : ∑ k : Fin q, ENNReal.ofReal (CH2 i l k) * holderENorm C.dl α V (D [k]) ≤
          ENNReal.ofReal M2 * ∑ k : Fin q, holderENorm C.dl α V (D [k]) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ =>
          mul_le_mul' (ENNReal.ofReal_le_ofReal (hM2 (i, l, k))) le_rfl
      exact (bE1.const_mul hM20).mono_left this
    have bt3 : BoundedBy (ENNReal.ofReal (CH3 i l) * holderENorm C.dl α V v) Y (M3 * C₃) := by
      have : ENNReal.ofReal (CH3 i l) * holderENorm C.dl α V v ≤
          ENNReal.ofReal M3 * holderENorm C.dl α V v :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (hM3 (i, l))) le_rfl
      exact (bv.const_mul hM30).mono_left this
    have hs12 := (bt1.add bt2 hM10 (mul_nonneg hM20 hcE0))
    have hs123 := hs12.add bt3 (add_nonneg hM10 (mul_nonneg hM20 hcE0)) (mul_nonneg hM30 hC₃.le)
    refine BoundedBy.mono_left hs123 ?_
    exact h1.trans (add_le_add (h2.trans (add_le_add t1 (h3.trans
      (Finset.sum_le_sum fun k _ => t2 k)))) t3)
  -- the empty word
  have hnil := holderWeakJet_nil_eqOn_noDrift (C := C) (V := F.V) hF.lifted.subset_U hα0 hvc
    (hD [] (S.nil_mem_wordFamily _ _)).1 (lt_top_iff_ne_top.2 (hD [] (S.nil_mem_wordFamily _ _)).2)
  have b00 : BoundedBy (holderENorm C.dl α V (D [])) Y C₃ := by
    rw [S.holderENorm_congr C.dl α V _ hnil]
    exact bv
  -- total
  have bpairsum : BoundedBy (∑ i : Fin q, ∑ l : Fin q, holderENorm C.dl α V (D [i, l])) Y
      (q * (q * cP)) := by
    have hin : ∀ i : Fin q, BoundedBy (∑ l : Fin q, holderENorm C.dl α V (D [i, l])) Y
        (q * cP) := fun i => by
      have := BoundedBy.sum_const (Finset.univ : Finset (Fin q)) (fun l _ => bpair i l) hcP0
      simpa using this
    have := BoundedBy.sum_const (Finset.univ : Finset (Fin q)) (fun i _ => hin i)
      (mul_nonneg hqq hcP0)
    simpa using this
  have hall := ((b00.add bE1 hC₃.le hcE0).add bpairsum (by positivity) (by positivity))
  have hfin := (jetENormNoDrift_le C.dl α V D).trans hall
  refine hfin.trans ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end RothschildStein.P2

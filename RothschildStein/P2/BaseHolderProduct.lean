-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderJet
public import RothschildStein.P2.HolderInterpolationLocal
public import RothschildStein.P2.ProductAbsorptionHolder
public import RothschildStein.P2.ProductAbsorptionCutoffs

/-!
# Leibniz jets of cutoff products, zero-extended to the frame patch

The zero-extension product estimates (BB p. 593; weak product rules, compact-support extension (BB Cor 2.10) and a first
exit argument). For a smooth cutoff `ζ` with `tsupport ζ` compact inside an open
`P ⊆ F.V` and `u` with a Hölder weak jet `D` on `P`, the Leibniz jet `prodJet C.Xl ζ u D` of `u ζ` is a
Hölder weak jet of `u ζ` on the whole patch `F.V`: the weak identities are those of `P` extended by
zero, and the Hölder norms on `F.V` and on `P` agree (`holderENorm_eq_of_compact_support_open`). Hence
`u ζ` lies in the compact intrinsic class `C^{2,α}_{X̃,0}(F.V)` (with the `(HD)` package of the
lifted chart).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart driftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The first and second `X̃`-derivatives of a smooth compactly supported `ζ` with
`tsupport ζ ⊆ C.U` are smooth with compact support inside `tsupport ζ`. -/
theorem cutoff_derivative_data_tsupport {ζ : (Fin (n + m) → ℝ) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hU : tsupport ζ ⊆ C.U) :
    (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) ζ)) ∧
    (∀ i, HasCompactSupport (fieldDerivative (C.Xl i) ζ)) ∧
    (∀ i, tsupport (fieldDerivative (C.Xl i) ζ) ⊆ tsupport ζ) ∧
    (∀ j i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) ζ))) ∧
    (∀ j i, HasCompactSupport (fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) ζ))) ∧
    (∀ j i, tsupport (fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) ζ)) ⊆ tsupport ζ) := by
  have h1 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) ζ) := fun i =>
    LiftedChart.contDiff_fieldDerivative_Xl hζ hU i
  have s1 : ∀ i, tsupport (fieldDerivative (C.Xl i) ζ) ⊆ tsupport ζ := fun i =>
    tsupport_fieldDerivative_subset _ _
  have s2 : ∀ j i, tsupport (fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) ζ)) ⊆ tsupport ζ :=
    fun j i => (tsupport_fieldDerivative_subset _ _).trans (s1 i)
  refine ⟨h1, fun i => hζc.of_isClosed_subset (isClosed_tsupport _) (s1 i), s1, fun j i => ?_,
    fun j i => hζc.of_isClosed_subset (isClosed_tsupport _) (s2 j i), s2⟩
  exact LiftedChart.contDiff_fieldDerivative_Xl (h1 i) ((s1 i).trans hU) j

/-- Products with a smooth compactly supported multiplier keep finite Hölder norm on any open
`P ⊆ C.U` containing its support (the continuity theorem and the Leibniz rule in `C^{k,α}_{X̃}`). -/
theorem holderENorm_mul_ne_top_on {P : Set (Fin (n + m) → ℝ)} (hP : IsOpen P) (hPU : P ⊆ C.U)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {b : (Fin (n + m) → ℝ) → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b) (hbP : tsupport b ⊆ P)
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α P f ≠ ⊤) :
    holderENorm C.dl α P (fun x => f x * b x) ≠ ⊤ := by
  obtain ⟨K, -, hK⟩ := LiftedChart.exists_holderENorm_mul_le (C := C) hP hPU hb hbc hbP hα0 hα1
  have e : (fun x => f x * b x) = fun x => b x * f x := funext fun x => mul_comm _ _
  rw [e]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf) (hK f)

/-- The Leibniz jet vanishes off the support of the multiplier. -/
theorem prodJet_eq_zero_of_notMem_tsupport {ζ u : (Fin (n + m) → ℝ) → ℝ}
    {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ} {z : Fin (n + m) → ℝ}
    (hz : z ∉ tsupport ζ) {I : List (Fin (q + 1))} (hI : I ∈ wordFamily driftWeight 2) :
    prodJet C.Xl ζ u D I z = 0 := by
  have h0 : ζ z = 0 := image_eq_zero_of_notMem_tsupport hz
  rcases wordFamily_drift_cases hI with rfl | ⟨i, rfl⟩ | ⟨j, i, rfl⟩
  · simp [prodJet, h0]
  · simp [prodJet, h0, fieldDerivative_eq_zero_of_notMem_tsupport hz]
  · simp [prodJet, h0, fieldDerivative_eq_zero_of_notMem_tsupport hz,
      fieldDerivative_fieldDerivative_eq_zero_of_notMem_tsupport hz]

/-- **The Leibniz jet of `u ζ` is a Hölder weak jet on the whole patch.**
Let `P ⊆ F.V` be open, `ζ` smooth with `tsupport ζ` compact in `P`, and `D` a Hölder weak jet of `u` on
`P`. Then `prodJet C.Xl ζ u D` is a Hölder weak jet of `u ζ` on `F.V` (weak identities extended by zero,
BB Cor 2.10; Hölder norms equal on `P` and `F.V`, first exit). -/
theorem isHolderWeakJet_prodJet_ext (hF : C.IsLiftedFrame F) {P : Opens (Fin (n + m) → ℝ)}
    (hPF : (P : Set (Fin (n + m) → ℝ)) ⊆ F.V) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {ζ u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (hζP : tsupport ζ ⊆ (P : Set (Fin (n + m) → ℝ)))
    (hu : holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) u ≠ ⊤)
    (hD : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl P I u (D I) ∧
      holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) (D I) ≠ ⊤) :
    LiftedChart.IsHolderWeakJet driftWeight C.Xl C.dl F.V 2 α (fun x => u x * ζ x)
      (prodJet C.Xl ζ u D) := by
  classical
  have hPU : (P : Set (Fin (n + m) → ℝ)) ⊆ C.U := hPF.trans hF.subset_U
  have hXP : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (P : Set (Fin (n + m) → ℝ)) := fun i =>
    (hF.contDiffOn_Xl i).mono hPF
  have hζ' : ContDiffOn ℝ (⊤ : ℕ∞) ζ (P : Set (Fin (n + m) → ℝ)) := hζ.contDiffOn
  obtain ⟨c1, cc1, cs1, c2, cc2, cs2⟩ := cutoff_derivative_data_tsupport (C := C) hζ hζc
    (hζP.trans hPU)
  have hK : IsCompact (tsupport ζ) := hζc
  have hmul := fun {b f : (Fin (n + m) → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ tsupport ζ)
    (hf : holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) f ≠ ⊤) =>
    holderENorm_mul_ne_top_on (C := C) P.isOpen hPU hα0 hα1 hb hbc (hbs.trans hζP) hf
  have hadd : ∀ f g : (Fin (n + m) → ℝ) → ℝ,
      holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) f ≠ ⊤ →
      holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) g ≠ ⊤ →
      holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) (fun x => f x + g x) ≠ ⊤ :=
    fun f g hf hg => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, hg⟩)
      (holderENorm_add_le hα0.le _ _)
  have hum : ContinuousOn u (P : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hPU hα0 (lt_top_iff_ne_top.2 hu)
  have hmem1 : ∀ i : Fin q, [i.succ] ∈ wordFamily driftWeight 2 := fun i =>
    (S.mem_wordFamily_iff _ _ _).2 (by simp [wordWeight, driftWeight, Fin.succ_ne_zero])
  -- weak identities and finite Hölder norms on `P`
  have hP : ∀ I ∈ wordFamily driftWeight 2,
      hasWeakWordDeriv C.Xl P I (fun x => u x * ζ x) (prodJet C.Xl ζ u D I) ∧
        holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) (prodJet C.Xl ζ u D I) ≠ ⊤ := by
    intro I hI
    rcases wordFamily_drift_cases hI with rfl | ⟨i, rfl⟩ | ⟨j, i, rfl⟩
    · refine ⟨S.hasWeakWordDeriv_nil C.Xl P ((hum.mul hζ.continuous.continuousOn).locallyIntegrableOn
        P.isOpen.measurableSet), hmul hζ hζc le_rfl hu⟩
    · obtain ⟨hw1, hh1⟩ := hD [i] hI
      exact ⟨hasWeakWordDeriv_prodJet_single hXP hζ' i hw1,
        hadd _ _ (hmul hζ hζc le_rfl hh1) (hmul (c1 i) (cc1 i) (cs1 i) hu)⟩
    · have hmj := hmem1 j
      have hmi := hmem1 i
      obtain ⟨hwi, hhi⟩ := hD [i.succ] hmi
      obtain ⟨hwj, hhj⟩ := hD [j.succ] hmj
      obtain ⟨hwji, hhji⟩ := hD [j.succ, i.succ] hI
      refine ⟨hasWeakWordDeriv_prodJet_pair hXP hζ' j.succ i.succ hwi hwj hwji, ?_⟩
      exact hadd _ _ (hadd _ _ (hmul hζ hζc le_rfl hhji)
        (hmul (c1 j.succ) (cc1 j.succ) (cs1 j.succ) hhi))
        (hadd _ _ (hmul (c1 i.succ) (cc1 i.succ) (cs1 i.succ) hhj)
          (hmul (c2 j.succ i.succ) (cc2 j.succ i.succ) (cs2 j.succ i.succ) hu))
  intro I hI
  obtain ⟨hweakP, hfinP⟩ := hP I hI
  have hz : ∀ z ∈ (F.V : Set (Fin (n + m) → ℝ)) \ tsupport ζ, prodJet C.Xl ζ u D I z = 0 :=
    fun z hz => prodJet_eq_zero_of_notMem_tsupport hz.2 hI
  have hzf : ∀ z, z ∉ tsupport ζ → (fun x => u x * ζ x) z = 0 := fun z hz => by
    simp [image_eq_zero_of_notMem_tsupport hz]
  refine ⟨?_, ?_⟩
  · have hext := S.hasWeakWordDeriv_zeroExtension C.Xl F.V P hPF ⟨tsupport ζ, hK⟩ hζP I
      (fun x => u x * ζ x) (prodJet C.Xl ζ u D I) hweakP
      (Eventually.of_forall fun x _ hxK => hzf x hxK)
    have e1 : (P : Set (Fin (n + m) → ℝ)).indicator (fun x => u x * ζ x) =
        fun x => u x * ζ x := by
      funext x
      by_cases hx : x ∈ (P : Set (Fin (n + m) → ℝ))
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        exact (hzf x (fun h => hx (hζP h))).symm
    have e2 : (P : Set (Fin (n + m) → ℝ)).indicator (prodJet C.Xl ζ u D I) =
        prodJet C.Xl ζ u D I := by
      funext x
      by_cases hx : x ∈ (P : Set (Fin (n + m) → ℝ))
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, prodJet_eq_zero_of_notMem_tsupport (fun h => hx (hζP h)) hI]
    rw [e1, e2] at hext
    exact hext
  · have heq := holderENorm_eq_of_compact_support_open (Ω := C.O) (w := driftWeight) (X := C.Xl)
      driftWeight_le_two hα0 (prodJet C.Xl ζ u D I) hK P.isOpen hζP hPF hz
    change holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (prodJet C.Xl ζ u D I) ≠ ⊤
    have : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (prodJet C.Xl ζ u D I) =
        holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) (prodJet C.Xl ζ u D I) := heq
    rw [this]
    exact hfinP

/-- **`u ζ` lies in the compact intrinsic class on the whole patch**: for
`P`, `ζ`, `u`, `D` as in `isHolderWeakJet_prodJet_ext` and the product `u ζ` of finite Hölder norm,
`u ζ ∈ C^{2,α}_{X̃,0}(F.V)` (with the `(HD)` package of the lifted chart). -/
theorem memHolderXCompact_prod_ext (hF : C.IsLiftedFrame F) {P : Opens (Fin (n + m) → ℝ)}
    (hPF : (P : Set (Fin (n + m) → ℝ)) ⊆ F.V) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {ζ u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (hζP : tsupport ζ ⊆ (P : Set (Fin (n + m) → ℝ)))
    (hu : holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) u ≠ ⊤)
    (hD : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl P I u (D I) ∧
      holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) (D I) ≠ ⊤) :
    memHolderXCompact driftWeight C.Xl C.dl F.V 2 α (fun x => u x * ζ x) := by
  have hjet := isHolderWeakJet_prodJet_ext hF hPF hα0 hα1 hζ hζc hζP hu hD
  have hPU : (P : Set (Fin (n + m) → ℝ)) ⊆ C.U := hPF.trans hF.subset_U
  have hum : ContinuousOn u (P : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hPU hα0 (lt_top_iff_ne_top.2 hu)
  have hfin0 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => u x * ζ x) ≠ ⊤ :=
    (hjet [] (S.nil_mem_wordFamily _ _)).2
  have hweak : S.memWeakHolderX driftWeight C.Xl C.distanceGeometry.d F.V 2 α (fun x => u x * ζ x) :=
    ⟨lt_top_iff_ne_top.2 hfin0, fun I hI =>
      ⟨prodJet C.Xl ζ u D I, (hjet I hI).1, lt_top_iff_ne_top.2 (hjet I hI).2⟩⟩
  have hmem := S.memHolderX_of_memWeakHolderX C.chartOpens F.V C.distanceGeometry hF.subset_U
    driftWeight C.Xl hF.contDiffOn_Xl 2 hα0 hweak
  have hsub : closure ((F.V : Set (Fin (n + m) → ℝ)) ∩ Function.support (fun x => u x * ζ x)) ⊆
      tsupport ζ := by
    refine closure_minimal (fun x hx => ?_) (isClosed_tsupport ζ)
    exact subset_tsupport ζ (right_ne_zero_of_mul hx.2)
  exact ⟨hmem, hζc.of_isClosed_subset isClosed_closure hsub, hsub.trans (hζP.trans hPF)⟩

end RothschildStein.P2

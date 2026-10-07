-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderCutoff
public import RothschildStein.P2.TransferCoverHolderCover
public import RothschildStein.P1.WeakExtensionLocal

/-!
# Localization of a `C^{2,α}` function to the frame patch

Part of the base Hölder estimate (BB pp. 600–602; zero extension of compactly supported Hölder
functions, by a first-exit argument). The lifted base Hölder estimate is stated for
`u ∈ C^{2,α}_{X̃}(W)` on an arbitrary open neighbourhood `W` of the closed `ρ`-ball, while the compact
estimate and the Hölder interpolation inequalities live on the patch `F.V` of the frame. For an open
`B` with `closure B` compact in `W ∩ F.V` (here `B = U_s^ρ`), `exists_localization` produces a cutoff
`η ∈ C_c^∞(W ∩ F.V)`, `η = 1` near `closure B`, and the product `u' = η u` of the compact intrinsic class
`C^{2,α}_{X̃,0}(F.V)` with the Hölder weak jet `D' = prodJet η u D`, such that on `B`

* `u' = u`, `L̃D' = f` (for any intrinsic value `f = L̃u` of the operator on `W`), and
* for every open `V' ⊆ B`, `‖u‖_{C^{2,α}(V')} = ∑_I ‖D' I‖_{C^α(V')}` (`holderXENorm_eq_jetENorm`).

No value of `u` outside `closure B` enters the later estimates.
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

/-- The sum of the intrinsic values over the words of `driftOpWords` is `L̃` of the jet. -/
theorem sum_driftOpWords_jet (D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ)
    (x : Fin (n + m) → ℝ) :
    ∑ i : Fin (q + 1), D (driftOpWords q i) x = weakSumSquaresWithDrift D x := by
  rw [Fin.sum_univ_succ]
  simp [driftOpWords, weakSumSquaresWithDrift, Fin.succ_ne_zero]

/-- **Localization to the frame patch.** See the module docstring. -/
theorem exists_localization (hF : C.IsLiftedFrame F) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {W : Opens (Fin (n + m) → ℝ)} {u f : (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderX driftWeight C.Xl C.dl W 2 α u)
    (hf : HasIntrinsicOperatorValue C.Xl W (driftOpWords q) u f)
    {B : Opens (Fin (n + m) → ℝ)} (hBc : IsCompact (closure (B : Set (Fin (n + m) → ℝ))))
    (hBW : closure (B : Set (Fin (n + m) → ℝ)) ⊆ (W : Set (Fin (n + m) → ℝ)))
    (hBV : closure (B : Set (Fin (n + m) → ℝ)) ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    ∃ (u' : (Fin (n + m) → ℝ) → ℝ) (D' : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ),
      memHolderXCompact driftWeight C.Xl C.dl F.V 2 α u' ∧
      LiftedChart.IsHolderWeakJet driftWeight C.Xl C.dl F.V 2 α u' D' ∧
      (∀ x ∈ (B : Set (Fin (n + m) → ℝ)), u' x = u x) ∧
      (∀ x ∈ (B : Set (Fin (n + m) → ℝ)), weakSumSquaresWithDrift D' x = f x) ∧
      ∀ V' : Opens (Fin (n + m) → ℝ), (V' : Set (Fin (n + m) → ℝ)) ⊆ B →
        holderXENorm driftWeight C.Xl C.dl V' 2 α u = jetENorm C.dl α (V' : Set (Fin (n + m) → ℝ)) D' := by
  classical
  set P : Opens (Fin (n + m) → ℝ) := W ⊓ F.V with hP
  have hPW : (P : Set (Fin (n + m) → ℝ)) ⊆ W := fun x hx => hx.1
  have hPV : (P : Set (Fin (n + m) → ℝ)) ⊆ F.V := fun x hx => hx.2
  have hPU : (P : Set (Fin (n + m) → ℝ)) ⊆ C.U := hPV.trans hF.subset_U
  have hBP : closure (B : Set (Fin (n + m) → ℝ)) ⊆ (P : Set (Fin (n + m) → ℝ)) := fun x hx =>
    ⟨hBW hx, hBV hx⟩
  have hXP : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (P : Set (Fin (n + m) → ℝ)) := fun i =>
    (hF.contDiffOn_Xl i).mono hPV
  have huP : memHolderX driftWeight C.Xl C.dl P 2 α u :=
    memHolderX_mono_domain driftWeight hPW hu
  obtain ⟨D, hDnil, hDP⟩ := exists_weakJet_of_memHolderX (C := C) (V := P) hPU hXP hα0 huP
  have hDfin : ∀ I ∈ wordFamily driftWeight 2, hasWeakWordDeriv C.Xl P I u (D I) ∧
      holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) (D I) ≠ ⊤ := fun I hI =>
    ⟨(hDP I hI).1, (hDP I hI).2.ne⟩
  have huFin : holderENorm C.dl α (P : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := huP.1.ne
  have hucont : ContinuousOn u (P : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hPU hα0 huP.1
  -- the cutoff
  obtain ⟨η, W', hW'o, hBW', hW'P, hη1⟩ := exists_test_eq_on_nhds P hBc hBP
    (u := fun _ => (1 : ℝ)) contDiffOn_const
  have hη1' : EqOn (η : (Fin (n + m) → ℝ) → ℝ) (fun _ => 1) W' := fun x hx => hη1 x hx
  let W'o : Opens (Fin (n + m) → ℝ) := ⟨W', hW'o⟩
  have hBsubW' : (B : Set (Fin (n + m) → ℝ)) ⊆ W' := subset_closure.trans hBW'
  have hηeq : ∀ I ∈ wordFamily driftWeight 2, EqOn (prodJet C.Xl η u D I) (D I) W' := fun I hI =>
    prodJet_eqOn_of_eqOn_one (C := C) (U := W'o) hη1' (fun x _ => by rw [hDnil]) hI
  -- intrinsic derivatives on `P`
  have hintr := holderWeakJet_hasIntrinsicWordDeriv (C := C) hPU hXP hα0 hucont
    (fun I hI => ⟨(hDP I hI).1, (hDP I hI).2⟩)
  refine ⟨fun x => u x * η x, prodJet C.Xl η u D, ?_, ?_, ?_, ?_, ?_⟩
  · exact memHolderXCompact_prod_ext hF (P := P) hPV hα0 hα1 η.contDiff η.hasCompactSupport
      η.tsupport_subset huFin hDfin
  · exact isHolderWeakJet_prodJet_ext hF (P := P) hPV hα0 hα1 η.contDiff η.hasCompactSupport
      η.tsupport_subset huFin hDfin
  · intro x hx
    simp [hη1' (hBsubW' hx)]
  · intro x hx
    obtain ⟨g, hg, hfg⟩ := hf
    have hxW : x ∈ (W : Set (Fin (n + m) → ℝ)) := hBW (subset_closure hx)
    have hxP : x ∈ (P : Set (Fin (n + m) → ℝ)) := hBP (subset_closure hx)
    rw [← hfg x hxW, ← sum_driftOpWords_jet (prodJet C.Xl η u D)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmem : driftOpWords q i ∈ wordFamily driftWeight 2 := driftOpWords_mem_wordFamily q i
    have hgP : hasIntrinsicWordDeriv C.Xl P (driftOpWords q i) u (g i) :=
      hasIntrinsicWordDeriv_mono hPW _ (hg i)
    have huniq := S.hasIntrinsicWordDeriv_unique P C.Xl (driftOpWords q i) hgP (hintr _ hmem)
    rw [hηeq _ hmem (hBsubW' hx), ← huniq hxP]
  · intro V' hV'B
    have hV'W : (V' : Set (Fin (n + m) → ℝ)) ⊆ W := fun x hx => hBW (subset_closure (hV'B hx))
    have hV'P : (V' : Set (Fin (n + m) → ℝ)) ⊆ P := fun x hx => hBP (subset_closure (hV'B hx))
    have hV'U : (V' : Set (Fin (n + m) → ℝ)) ⊆ C.U := hV'P.trans hPU
    have hXV' : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V' : Set (Fin (n + m) → ℝ)) := fun i =>
      (hXP i).mono hV'P
    have huV' : memHolderX driftWeight C.Xl C.dl V' 2 α u := memHolderX_mono_domain driftWeight hV'W hu
    have h1 := holderXENorm_eq_jetENorm (C := C) hV'U hXV' hα0 huV' (D := D) (fun I hI =>
      ⟨S.hasWeakWordDeriv_restrict C.Xl P V' hV'P (hDP I hI).1,
        lt_of_le_of_lt (S.holderENorm_mono C.dl α _ _ hV'P) (hDP I hI).2⟩)
    rw [h1]
    exact jetENorm_congr fun I hI => ((hηeq I hI).mono fun x hx => hBsubW' (hV'B hx)).symm

end RothschildStein.P2

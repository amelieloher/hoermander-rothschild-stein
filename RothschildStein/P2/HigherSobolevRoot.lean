-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevChart
public import RothschildStein.P2.LocalRegularityCoreNoDrift
public import RothschildStein.P2.SmoothingTheorem
public import RothschildStein.H3.FiniteCoverSobolevNorm

/-!
# Higher Sobolev regularity without drift on the original domain (BB Thm 11.45, Props 11.46-11.47)

`higherSobolevRegularityNoDrift_of_hypotheses` proves the Prop `HigherSobolevRegularityNoDrift` (`LocalRegularityHypotheses`) from the exact
upstream statements `LiftApproximationNoDriftStatement` (the lifting theorem, giving lifted charts), `TypeCalculusAllChartsNoDrift`
(row integrability, differentiation and transfer), `SignedParametrixAllChartsNoDrift` (the signed parametrix) and `LiftedBaseSobolevAllChartsNoDrift` (the base Sobolev estimate, no drift): for
`Ω' ⋐ Ω'' ⋐ Ω`, every `u ∈ W^{2,p}_X(Ω'')` with `L u = f ∈ W^{k,p}_X(Ω'')` lies in `W^{k+2,p}_X(Ω')` and
`‖u‖_{W^{k+2,p}(Ω')} ≤ C (‖f‖_{W^{k,p}(Ω'')} + ‖u‖_{L^p(Ω'')})`.

Proof (BB pp. 588–591).

1. *Regularity without presupposing it.* At every point `x ∈ Ω''` a lifted chart gives
   `LiftedHigherRegularity` (`liftedRegularity`, from the compact-support regularity step `regularityStep` =
   the higher-order representation on `W_0` and the higher-order gain, with the cutoff `η u` of `cutoffRegularity`, iterated on halved `ρ`-balls) and the
   local descent `higher_local_regularity` gives `u ∈ W^{k+2,p}_X(A_x)` on a neighborhood; the local pieces
   glue (`memSobolevXLoc_of_local`) to `u ∈ W^{k+2,p}_X(V)` on every `V ⋐ Ω''`.
2. *The estimate.* At every point of `closure Ω'` the lifted a priori estimate (`liftedEstimate`: the base
   Sobolev estimate and the cutoff recurrence `cutoffEstimate`, `compactRecurrence`) transfers to a small base
   ball (`higher_local_transfer`, the lifted Sobolev norm transfer); a finite cover of `closure Ω'` and the finite-cover inequality for
   the Sobolev norm give the estimate.
3. `q = 0` is trivial (the only word is empty).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

/-- The system without vector fields (`q = 0`): every weak word is the empty word, so the statement of
The higher Sobolev estimate reduces to the restriction `W^{2,p}_X(Ω'') → L^p(Ω')`. -/
theorem higherSobolev_zero_alphabet {n : ℕ} (Ω' Ω'' : Opens (Fin n → ℝ))
    (hsub : (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)))
    (X : Fin 0 → (Fin n → ℝ) → (Fin n → ℝ)) (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (u f : (Fin n → ℝ) → ℝ) (hu : memSobolevX noDriftWeight X Ω'' 2 p u) :
    memSobolevX noDriftWeight X Ω' (k + 2) p u ∧
      sobolevXENorm noDriftWeight X Ω' (k + 2) p u ≤
        ENNReal.ofReal 1 * (sobolevXENorm noDriftWeight X Ω'' k p f +
          eLpNorm u p (volume.restrict (Ω'' : Set (Fin n → ℝ)))) := by
  have hI0 : ∀ I : List (Fin 0), I = [] := fun I => by
    cases I with
    | nil => rfl
    | cons a I => exact a.elim0
  have hu' := RothschildStein.S.memSobolevX_restrict noDriftWeight X Ω'' Ω' hsub hu
  refine ⟨⟨hu'.1, fun I hI => ?_⟩, ?_⟩
  · rw [hI0 I]
    exact hu'.2 [] (RothschildStein.S.nil_mem_wordFamily _ 2)
  · have hloc : LocallyIntegrableOn u (Ω' : Set (Fin n → ℝ)) volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict (hu'.1.locallyIntegrable hp)
    have hsubset : wordFamily noDriftWeight (k + 2) ⊆ ({[]} : Finset (List (Fin 0))) := fun I _ => by
      rw [hI0 I]
      simp
    unfold sobolevXENorm
    calc ∑ I ∈ wordFamily noDriftWeight (k + 2), weakWordENorm X Ω' I p u
        ≤ ∑ I ∈ ({[]} : Finset (List (Fin 0))), weakWordENorm X Ω' I p u :=
          Finset.sum_le_sum_of_subset hsubset
      _ = weakWordENorm X Ω' [] p u := Finset.sum_singleton _ _
      _ = eLpNorm u p (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
          RothschildStein.S.weakWordENorm_eq X Ω' [] p u u
            (RothschildStein.S.hasWeakWordDeriv_nil X Ω' hloc)
      _ ≤ eLpNorm u p (volume.restrict (Ω'' : Set (Fin n → ℝ))) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
      _ ≤ ENNReal.ofReal 1 * (sobolevXENorm noDriftWeight X Ω'' k p f +
          eLpNorm u p (volume.restrict (Ω'' : Set (Fin n → ℝ)))) := by
          rw [ENNReal.ofReal_one, one_mul]
          exact le_add_self

/-- **Higher Sobolev regularity, no drift** (BB pp. 588-591, Thm 11.45, Props 11.46-11.47, (11.73)-(11.74)):
the Prop `HigherSobolevRegularityNoDrift` (`LocalRegularityHypotheses`), assuming the lifting theorem statement
(`LiftApproximationNoDriftStatement`, which supplies the lifted charts), the upstream statements `TypeCalculusAllChartsNoDrift`
(row integrability, differentiation and transfer) and `SignedParametrixAllChartsNoDrift` (the signed parametrix) for the standard frames of the charts, and the lifted base
estimate `LiftedBaseSobolevAllChartsNoDrift` (the base Sobolev estimate). -/
theorem higherSobolevRegularityNoDrift_of_hypotheses (R1 : LiftApproximationNoDriftStatement) (h1 : TypeCalculusAllChartsNoDrift)
    (hParametrix : SignedParametrixAllChartsNoDrift) (hlift : LiftedBaseSobolevAllChartsNoDrift) : HigherSobolevRegularityNoDrift := by
  intro n q hn3 Ω Ω' Ω'' X hX hspan hc' hs' hc'' hs'' k p hp hpt
  have hP : (1 : ℝ≥0∞) ≤ p := hp.le
  have hPt : p ≠ ⊤ := hpt.ne
  have hΩ''Ω : (Ω'' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := subset_closure.trans hs''
  have hΩ'Ω'' : (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) := subset_closure.trans hs'
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨1, one_pos, fun u f hu _ _ => higherSobolev_zero_alphabet Ω' Ω'' hΩ'Ω'' X k hP u f hu⟩
  have hn : 0 < n := by omega
  obtain ⟨W₁, hW₁sub, hW₁c, hW₁Ω''⟩ := exists_open_between_closure Ω'' Ω' hc' hs'
  have hchart := hchart_noDrift R1 hn hq Ω X hX hspan
  have hxΩ : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), x ∈ (Ω : Set (Fin n → ℝ)) :=
    fun x hx => hΩ''Ω (hs' hx)
  -- the local transfer at every point of `closure Ω'`
  have hloc : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧
      rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x b ⊆ (W₁ : Set (Fin n → ℝ)) ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)),
        (Vρ : Set (Fin n → ℝ)) = rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x b →
        ∀ u f : (Fin n → ℝ) → ℝ,
        memSobolevX noDriftWeight X Vb (k + 2) p u →
        HasWeakOperatorValue X Vb (noDriftOpWords q) u f →
        memSobolevX noDriftWeight X Vb k p f →
        sobolevXENorm noDriftWeight X Vρ (k + 2) p u ≤ ENNReal.ofReal K *
          (sobolevXENorm noDriftWeight X Vb k p f +
            eLpNorm u p (volume.restrict (Vb : Set (Fin n → ℝ)))) := by
    intro x hx
    obtain ⟨s, m, ⟨C⟩⟩ := hchart x (hxΩ x hx)
    obtain ⟨-, hest⟩ := chart_higher_of_upstream h1 hParametrix hlift hn3 hq C hp hpt k
    obtain ⟨ε, hε0, hεV⟩ := exists_rsBall_subset (w := noDriftWeight) Ω.isOpen (fun i => (hX i).continuousOn) W₁.isOpen
      (hW₁sub hx) (hxΩ x hx)
    obtain ⟨ρ, b, K, hρ, hρb, hbε, hK, hopen, hbound⟩ :=
      higher_local_transfer C (G2.smoothNorm C.G) (noDriftOpWords q) hP hPt hest hε0
    exact ⟨ρ, b, K, hρ, hρb, (rsBall_mono (Ω : Set (Fin n → ℝ)) noDriftWeight X x hbε).trans hεV,
      hK, hopen, hbound⟩
  -- regularity on `W₁`
  have hX'' : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω'' : Set (Fin n → ℝ)) :=
    fun i => (hX i).mono hΩ''Ω
  have hreg : ∀ u f : (Fin n → ℝ) → ℝ, memSobolevX noDriftWeight X Ω'' 2 p u →
      HasWeakOperatorValue X Ω'' (noDriftOpWords q) u f → memSobolevX noDriftWeight X Ω'' k p f →
      memSobolevX noDriftWeight X W₁ (k + 2) p u := by
    intro u f hu hop hf
    have hlocal : ∀ x ∈ (Ω'' : Set (Fin n → ℝ)), ∃ A : Opens (Fin n → ℝ),
        x ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ Ω'' ∧ memSobolevX noDriftWeight X A (k + 2) p u := by
      intro x hx
      obtain ⟨s, m, ⟨C⟩⟩ := hchart x (hΩ''Ω hx)
      obtain ⟨hregC, -⟩ := chart_higher_of_upstream h1 hParametrix hlift hn3 hq C hp hpt k
      obtain ⟨A, hxA, hAW, hmem⟩ := higher_local_regularity C (G2.smoothNorm C.G) (noDriftOpWords q)
        hP hPt hregC hx hΩ''Ω hu hop hf
      exact ⟨A, hxA, hAW, hmem⟩
    have hFloc : LocallyIntegrableOn u (Ω'' : Set (Fin n → ℝ)) volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict (hu.1.locallyIntegrable hP)
    have hLoc := memSobolevXLoc_of_local noDriftWeight X Ω'' hX'' (zero_lt_one.trans_le hP).ne' hPt
      hFloc hlocal
    exact hLoc W₁ hW₁c hW₁Ω''
  -- the finite cover
  choose ρ b K hρ0 hρb hbW hK0 hopen hbound using hloc
  have hnhds : ∀ x (hx : x ∈ closure (Ω' : Set (Fin n → ℝ))),
      rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x (ρ x hx) ∈ 𝓝 x := fun x hx =>
    (hopen x hx _ (hρ0 x hx) (hρb x hx)).mem_nhds
      ⟨hxΩ x hx, by
        rw [G1.controlDistance_self noDriftWeight X (hxΩ x hx)]
        exact ENNReal.ofReal_pos.2 (hρ0 x hx)⟩
  obtain ⟨t, ht⟩ := hc'.elim_nhds_subcover'
    (fun x hx => rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x (ρ x hx)) hnhds
  let A : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ) := fun x =>
    ⟨rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x.1 (ρ x.1 x.2),
      hopen x.1 x.2 _ (hρ0 x.1 x.2) (hρb x.1 x.2)⟩
  let B : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ) := fun x =>
    ⟨rsBall (Ω : Set (Fin n → ℝ)) noDriftWeight X x.1 (b x.1 x.2),
      hopen x.1 x.2 _ ((hρ0 x.1 x.2).trans_le (hρb x.1 x.2)) le_rfl⟩
  have hBW : ∀ x, (B x : Set (Fin n → ℝ)) ⊆ (W₁ : Set (Fin n → ℝ)) := fun x => hbW x.1 x.2
  have hAW : ∀ x, (A x : Set (Fin n → ℝ)) ⊆ (W₁ : Set (Fin n → ℝ)) := fun x =>
    (rsBall_mono (Ω : Set (Fin n → ℝ)) noDriftWeight X x.1 (hρb x.1 x.2)).trans (hbW x.1 x.2)
  have hKsum : 0 ≤ ∑ x ∈ t, K x.1 x.2 := Finset.sum_nonneg fun x _ => (hK0 x.1 x.2).le
  refine ⟨1 + ∑ x ∈ t, K x.1 x.2, by linarith, fun u f hu hop hf => ?_⟩
  have hu₁ := hreg u f hu hop hf
  refine ⟨RothschildStein.S.memSobolevX_restrict noDriftWeight X W₁ Ω'
    (subset_closure.trans hW₁sub) hu₁, ?_⟩
  have hcov := RothschildStein.H3.sobolevXENorm_le_finite_open_cover noDriftWeight X W₁ Ω' t A
    (subset_closure.trans hW₁sub) (fun x _ => hAW x)
    (fun y hy => by
      have := ht (subset_closure hy)
      simp only [mem_iUnion] at this
      obtain ⟨x, hx, hyx⟩ := this
      exact ⟨x, hx, hyx⟩) (k + 2) p hP u hu₁
  refine hcov.trans ?_
  set N : ℝ≥0∞ := sobolevXENorm noDriftWeight X Ω'' k p f +
    eLpNorm u p (volume.restrict (Ω'' : Set (Fin n → ℝ))) with hN
  calc ∑ x ∈ t, sobolevXENorm noDriftWeight X (A x) (k + 2) p u
      ≤ ∑ x ∈ t, ENNReal.ofReal (K x.1 x.2) * N := by
        refine Finset.sum_le_sum fun x _ => ?_
        have hBΩ'' : (B x : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) :=
          (hBW x).trans (subset_closure.trans hW₁Ω'')
        refine (hbound x.1 x.2 (A x) (B x) rfl rfl u f
          (RothschildStein.S.memSobolevX_restrict noDriftWeight X W₁ (B x) (hBW x) hu₁)
          (HasWeakOperatorValue.mono hBΩ'' hop)
          (RothschildStein.S.memSobolevX_restrict noDriftWeight X Ω'' (B x) hBΩ'' hf)).trans ?_
        refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
        · exact sobolevXENorm_mono_domain noDriftWeight X hBΩ'' hf
        · exact eLpNorm_mono_measure _ (Measure.restrict_mono hBΩ'' le_rfl)
    _ = ENNReal.ofReal (∑ x ∈ t, K x.1 x.2) * N := by
        rw [ENNReal.ofReal_sum_of_nonneg fun x _ => (hK0 x.1 x.2).le, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (1 + ∑ x ∈ t, K x.1 x.2) * N :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end RothschildStein.P2

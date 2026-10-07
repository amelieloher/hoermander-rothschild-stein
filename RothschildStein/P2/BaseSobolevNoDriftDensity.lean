-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseSobolevNoDriftCompact
public import RothschildStein.P2.SobolevInterpolationNoDriftDensity

/-!
# No drift: from tests to `W^{2,p}_{X̃,0}`

The compact second-derivative estimate `CompactSecondOnNoDrift` is proved for test functions
(`exists_compactSecond_noDrift_of_representation`). For `f` in the closure of the tests in the weighted
Sobolev norm (`memSobolevXZero`, BB Cor 2.10) it passes to the limit: if `Ω' ≤ V` and `a = 1` on `Ω'`, then
for every word `I` of weight two

`‖X̃_I f‖_{L^p(Ω')} ≤ Λ (‖L̃ f‖_{L^p(Ω')} + ‖f‖_{L^p(Ω')})`

(`weakWordENorm_second_of_zero_noDrift`), where `L̃ f` is any a.e. representative of `∑ₗ g₂ₗ`, the weak
derivatives of the words `[l, l]`. The approximants are the tests of the definition of `memSobolevXZero`;
the errors in the weak words are bounded by the Sobolev distance.
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

section Errors

/-- The error of a weak word derivative against the classical word derivative of a test
approximant is bounded by the Sobolev distance of order two (no drift). -/
theorem eLpNorm_weakWord_sub_le_noDrift {Ω' : Opens (Fin n → ℝ)}
    (hXΩ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω' : Set (Fin n → ℝ))) {P : ℝ≥0∞}
    {I : List (Fin q)} (hI : I ∈ wordFamily w 2) {f g : (Fin n → ℝ) → ℝ}
    (hg : hasWeakWordDeriv X Ω' I f g) (ψ : TestFunction Ω' ℝ (⊤ : ℕ∞)) :
    eLpNorm (fun x => g x - wordDerivative X I (ψ : (Fin n → ℝ) → ℝ) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      sobolevXENorm w X Ω' 2 P (fun x => f x - ψ x) := by
  have hs := S.hasWeakWordDeriv_sub X Ω' hXΩ hg
    (S.hasWeakWordDeriv_classical Ω' X hXΩ I ψ ψ.contDiff.contDiffOn)
  rw [← S.weakWordENorm_eq X Ω' I P _ _ hs]
  exact Finset.single_le_sum (f := fun I => weakWordENorm X Ω' I P (fun x => f x - ψ x))
    (fun _ _ => zero_le) hI

variable {V Ω' : Opens (Fin n → ℝ)}

/-- A smooth function supported in `Ω' ≤ V` has the same `L^p` norm of every classical word
derivative on `V` and on `Ω'` (no-drift alphabet). -/
theorem eLpNorm_wordDerivative_restrict_eq_noDrift (hΩ'V : Ω' ≤ V)
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ))) {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFs : tsupport F ⊆ (Ω' : Set (Fin n → ℝ)))
    (I : List (Fin q)) (P : ℝ≥0∞) :
    eLpNorm (wordDerivative X I F) P (volume.restrict (V : Set (Fin n → ℝ))) =
      eLpNorm (wordDerivative X I F) P (volume.restrict (Ω' : Set (Fin n → ℝ))) := by
  have hcont : ContinuousOn (wordDerivative X I F) (V : Set (Fin n → ℝ)) :=
    (S.contDiffOn_wordDerivative V X hXV I F hF.contDiffOn).continuousOn
  have hsupp : Function.support (wordDerivative X I F) ⊆ (Ω' : Set (Fin n → ℝ)) := fun x hx =>
    hFs (S.tsupport_wordDerivative_subset X I F (subset_tsupport _ hx))
  exact (eLpNorm_restrict_eq_of_support hΩ'V hcont hsupp P).symm

/-- A smooth function supported in `Ω' ≤ V` has the same `L^p` norm of `L̃ = ∑ᵢ X̃ᵢ²` on `V`
and on `Ω'` (no drift). -/
theorem eLpNorm_sumSquares_restrict_eq_noDrift (hΩ'V : Ω' ≤ V)
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ))) {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFs : tsupport F ⊆ (Ω' : Set (Fin n → ℝ))) (P : ℝ≥0∞) :
    eLpNorm (sumSquares X F) P (volume.restrict (V : Set (Fin n → ℝ))) =
      eLpNorm (sumSquares X F) P (volume.restrict (Ω' : Set (Fin n → ℝ))) := by
  have hD2 : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (X i) (fieldDerivative (X i) F)) (V : Set (Fin n → ℝ)) :=
    fun i => S.contDiffOn_fieldDerivative V (X i) _ (hXV _)
      (S.contDiffOn_fieldDerivative V (X i) F (hXV _) hF.contDiffOn)
  have hcont : ContinuousOn (sumSquares X F) (V : Set (Fin n → ℝ)) := by
    have h : sumSquares X F = fun x =>
        ∑ i : Fin q, fieldDerivative (X i) (fieldDerivative (X i) F) x := rfl
    rw [h]
    exact continuousOn_finsetSum _ fun i _ => (hD2 i).continuousOn
  have hsupp : Function.support (sumSquares X F) ⊆ (Ω' : Set (Fin n → ℝ)) := by
    intro x hx
    by_contra hxΩ
    exact hx (sumSquares_eq_zero_of_notMem_noDrift X F (fun h => hxΩ (hFs h)))
  exact (eLpNorm_restrict_eq_of_support hΩ'V hcont hsupp P).symm

end Errors

/-- **The compact second-derivative estimate for
`W^{2,p}_{X̃,0}`, no drift**: if `Ω' ≤ V` and `a = 1` on `Ω'`, `f ∈ W^{2,p}_{X̃,0}(Ω')` has weak
derivatives `g₂ₗ` of `[l, l]` on `Ω'` and `L̃ f` is an a.e. representative of `∑ₗ g₂ₗ`, then for every
word `I` of weight two `‖X̃_I f‖_{L^p(Ω')} ≤ Λ (‖L̃ f‖_{L^p(Ω')} + ‖f‖_{L^p(Ω')})` (weak norms on
`Ω'`). -/
theorem weakWordENorm_second_of_zero_noDrift
    (hw : ∀ j, (w j : ℕ) = 1) {V : Opens (Fin n → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p Λ : ℝ} (hp : 1 < p) (hCS : CompactSecondOnNoDrift w X V a p Λ)
    {Ω' : Opens (Fin n → ℝ)} (hΩ'V : Ω' ≤ V)
    (hΩ'a : ∀ x ∈ (Ω' : Set (Fin n → ℝ)), a x = 1) {f : (Fin n → ℝ) → ℝ}
    (hf : memSobolevXZero w X Ω' 2 (ENNReal.ofReal p) f)
    {g2 : Fin q → (Fin n → ℝ) → ℝ}
    (hg2 : ∀ l : Fin q, hasWeakWordDeriv X Ω' [l, l] f (g2 l))
    {Lf : (Fin n → ℝ) → ℝ}
    (hLf : Lf =ᵐ[volume.restrict (Ω' : Set (Fin n → ℝ))] fun x => ∑ l, g2 l x)
    {I : List (Fin q)} (hI : I ∈ wordsOfWeight w 2) :
    weakWordENorm X Ω' I (ENNReal.ofReal p) f ≤
      ENNReal.ofReal Λ * (eLpNorm Lf (ENNReal.ofReal p) (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        weakWordENorm X Ω' [] (ENNReal.ofReal p) f) := by
  classical
  obtain ⟨hfS, ψ, hψ⟩ := hf
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : (1 : ℝ≥0∞) ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hXΩ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω' : Set (Fin n → ℝ)) := fun i =>
    (hXV i).mono hΩ'V
  have hIw : I ∈ wordFamily w 2 := mem_wordFamily_two_of_mem_wordsOfWeight_two_noDrift hI
  have hmemN : ([] : List (Fin q)) ∈ wordFamily w 2 := S.nil_mem_wordFamily w 2
  obtain ⟨gI, hgI, -⟩ := hfS.2 I hIw
  obtain ⟨gN, hgN, -⟩ := hfS.2 [] hmemN
  have hLN : hasWeakWordDeriv X Ω' [] f f := S.hasWeakWordDeriv_nil X Ω' hgN.1
  have eI : weakWordENorm X Ω' I P f = eLpNorm gI P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ω' I P f gI hgI
  have eN : weakWordENorm X Ω' [] P f = eLpNorm f P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
    S.weakWordENorm_eq X Ω' [] P f f hLN
  rw [eI, eN]
  set E : ℕ → ℝ≥0∞ := fun j => sobolevXENorm w X Ω' 2 P (fun x => f x - ψ j x) with hE
  set cE : ℝ≥0∞ := ENNReal.ofReal Λ * ((q : ℝ≥0∞) + 1) + 1 with hcE
  have hcEtop : cE ≠ ⊤ := by
    rw [hcE]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_, ENNReal.one_ne_top⟩
    exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top q, ENNReal.one_ne_top⟩
  have hmain : ∀ j, eLpNorm gI P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
      ENNReal.ofReal Λ * (eLpNorm Lf P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm f P (volume.restrict (Ω' : Set (Fin n → ℝ)))) + cE * E j := by
    intro j
    have hψs : tsupport (ψ j : (Fin n → ℝ) → ℝ) ⊆ (Ω' : Set (Fin n → ℝ)) :=
      (ψ j).tsupport_subset
    have hψd : ContDiff ℝ (⊤ : ℕ∞) (ψ j : (Fin n → ℝ) → ℝ) := (ψ j).contDiff
    -- the errors
    have e2 := fun l : Fin q => eLpNorm_weakWord_sub_le_noDrift (w := w) hXΩ (P := P)
      (pair_mem_wordFamily_two_noDrift hw l l) (hg2 l) (ψ j)
    have eIj := eLpNorm_weakWord_sub_le_noDrift (w := w) hXΩ (P := P) hIw hgI (ψ j)
    have eNj := eLpNorm_weakWord_sub_le_noDrift (w := w) hXΩ (P := P) hmemN hLN (ψ j)
    -- the error in `L̃`
    have hLerr : eLpNorm (fun x => Lf x - sumSquares X (ψ j : (Fin n → ℝ) → ℝ) x) P
        (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤ (q : ℝ≥0∞) * E j := by
      have hae : (fun x => Lf x - sumSquares X (ψ j : (Fin n → ℝ) → ℝ) x) =ᵐ[volume.restrict
          (Ω' : Set (Fin n → ℝ))] fun x =>
          ∑ l : Fin q, (g2 l x - wordDerivative X [l, l] (ψ j : (Fin n → ℝ) → ℝ) x) := by
        filter_upwards [hLf] with x hx
        simp only [sumSquares, wordDerivative, Finset.sum_sub_distrib]
        rw [hx]
      rw [eLpNorm_congr_ae hae]
      have e : (fun x => ∑ l : Fin q, (g2 l x - wordDerivative X [l, l]
          (ψ j : (Fin n → ℝ) → ℝ) x)) = ∑ l : Fin q, fun x => g2 l x -
            wordDerivative X [l, l] (ψ j : (Fin n → ℝ) → ℝ) x := by
        funext x
        simp [Finset.sum_apply]
      rw [e]
      calc _ ≤ ∑ l : Fin q, eLpNorm (fun x => g2 l x - wordDerivative X [l, l]
              (ψ j : (Fin n → ℝ) → ℝ) x) P (volume.restrict (Ω' : Set (Fin n → ℝ))) :=
            eLpNorm_sum_le hP1
        _ ≤ ∑ _l : Fin q, E j := Finset.sum_le_sum fun l _ => e2 l
        _ = (q : ℝ≥0∞) * E j := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hL' := eLpNorm_le_add_sub' hP1 Lf (sumSquares X (ψ j : (Fin n → ℝ) → ℝ))
      (μ := volume.restrict (Ω' : Set (Fin n → ℝ)))
    have hN' := eLpNorm_le_add_sub' hP1 f (ψ j : (Fin n → ℝ) → ℝ)
      (μ := volume.restrict (Ω' : Set (Fin n → ℝ)))
    have hLbound : eLpNorm (sumSquares X (ψ j : (Fin n → ℝ) → ℝ)) P
        (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
        eLpNorm Lf P (volume.restrict (Ω' : Set (Fin n → ℝ))) + (q : ℝ≥0∞) * E j :=
      hL'.trans (add_le_add le_rfl hLerr)
    have hNbound : eLpNorm (ψ j : (Fin n → ℝ) → ℝ) P (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤
        eLpNorm f P (volume.restrict (Ω' : Set (Fin n → ℝ))) + E j :=
      hN'.trans (add_le_add le_rfl eNj)
    -- the estimate for the approximant
    have hCSj : eLpNorm (wordDerivative X I (ψ j : (Fin n → ℝ) → ℝ)) P
        (volume.restrict (V : Set (Fin n → ℝ))) ≤
        ENNReal.ofReal Λ * (eLpNorm (sumSquares X (ψ j : (Fin n → ℝ) → ℝ)) P
          (volume.restrict (V : Set (Fin n → ℝ))) +
          eLpNorm (ψ j : (Fin n → ℝ) → ℝ) P (volume.restrict (V : Set (Fin n → ℝ)))) :=
      hCS (extendTest hΩ'V (ψ j)) (fun x hx => hΩ'a x ((ψ j).tsupport_subset hx)) I hI
    rw [eLpNorm_wordDerivative_restrict_eq_noDrift hΩ'V hXV hψd hψs I P,
      eLpNorm_sumSquares_restrict_eq_noDrift hΩ'V hXV hψd hψs P,
      show eLpNorm (ψ j : (Fin n → ℝ) → ℝ) P (volume.restrict (V : Set (Fin n → ℝ))) =
        eLpNorm (wordDerivative X [] (ψ j : (Fin n → ℝ) → ℝ)) P
          (volume.restrict (V : Set (Fin n → ℝ))) from rfl,
      eLpNorm_wordDerivative_restrict_eq_noDrift hΩ'V hXV hψd hψs [] P] at hCSj
    have hI' := eLpNorm_le_add_sub hP1 gI (wordDerivative X I (ψ j : (Fin n → ℝ) → ℝ))
      (μ := volume.restrict (Ω' : Set (Fin n → ℝ)))
    calc eLpNorm gI P (volume.restrict (Ω' : Set (Fin n → ℝ)))
        ≤ eLpNorm (wordDerivative X I (ψ j : (Fin n → ℝ) → ℝ)) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) +
          eLpNorm (fun x => gI x - wordDerivative X I (ψ j : (Fin n → ℝ) → ℝ) x) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) := hI'
      _ ≤ ENNReal.ofReal Λ * ((eLpNorm Lf P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
            (q : ℝ≥0∞) * E j) +
          (eLpNorm f P (volume.restrict (Ω' : Set (Fin n → ℝ))) + E j)) + E j :=
        add_le_add (hCSj.trans (mul_le_mul' le_rfl (add_le_add hLbound
          (show eLpNorm (wordDerivative X [] (ψ j : (Fin n → ℝ) → ℝ)) P
            (volume.restrict (Ω' : Set (Fin n → ℝ))) ≤ _ from hNbound)))) eIj
      _ = _ := by rw [hcE]; ring
  have hlim : Tendsto (fun j => ENNReal.ofReal Λ *
      (eLpNorm Lf P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm f P (volume.restrict (Ω' : Set (Fin n → ℝ)))) + cE * E j) atTop
      (𝓝 (ENNReal.ofReal Λ * (eLpNorm Lf P (volume.restrict (Ω' : Set (Fin n → ℝ))) +
        eLpNorm f P (volume.restrict (Ω' : Set (Fin n → ℝ)))) + cE * 0)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hψ (Or.inr hcEtop))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim hmain

end RothschildStein.P2

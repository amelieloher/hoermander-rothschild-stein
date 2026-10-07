-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.WeakDerivativeLift
public import RothschildStein.P2.NormTransferLp
public import RothschildStein.Definitions.weakWordENorm
public import RothschildStein.Definitions.sobolevXENorm
public import RothschildStein.Definitions.wordFamily

/-!
# The weighted Sobolev norm transfer, abstractly

Given an `L^p` comparison constant `K` for the projection `π` between a lifted open set `Uo` and
base open sets `Vδ ⊆ Vo` (for `1 ≤ p < ∞` the constants `(c |U|/|V|)^{1/p}` of the fiber bounds,
for `p = ∞` the constant `1`), the weak-derivative lift gives the per-word and Sobolev-level
inequalities of the lifted norm transfer (BB pp. 584–585, Thms 11.40–11.41, (11.68)):

* `‖ũ‖_{W^{j,p}(Uo)} ≤ K₊ ‖u‖_{W^{j,p}(Vo)}` for every `u`;
* `K₋ ‖u‖_{W^{j,p}(Vδ)} ≤ ‖ũ‖_{W^{j,p}(Uo)}` when `u` is measurable and has its weak derivatives
  `X_I u` of order `I ≠ []`, `|I| ≤ j`, on `Vo`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2
variable {n m k : ℕ}

theorem sInf_le_mul_sInf {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKt : K ≠ ⊤) {S T : Set ℝ≥0∞}
    (h : ∀ r ∈ S, ∃ r' ∈ T, r' ≤ K * r) : sInf T ≤ K * sInf S := by
  have hS : sInf S = ⨅ r : S, (r : ℝ≥0∞) := sInf_eq_iInf' S
  rw [hS, ENNReal.mul_iInf_of_ne hK0 hKt]
  exact le_iInf fun r => by
    obtain ⟨r', hr', hle⟩ := h r r.2
    exact (sInf_le hr').trans hle

namespace FiberSetting

variable {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)} (S : FiberSetting Uo Vo)
include S

/-- per word, upper inequality: `‖X̃_I ũ‖_p ≤ K ‖X_I u‖_p`. -/
theorem weakWordENorm_lift_le (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ))) (I : List (Fin k))
    {p K : ℝ≥0∞} (hK0 : K ≠ 0) (hKt : K ≠ ⊤)
    (hlp : ∀ g : (Fin n → ℝ) → ℝ, AEStronglyMeasurable g (volume.restrict (Vo : Set (Fin n → ℝ))) →
      eLpNorm (fun ξ => g (basePoint ξ)) p (volume.restrict (Uo : Set (Fin (n + m) → ℝ))) ≤
        K * eLpNorm g p (volume.restrict (Vo : Set (Fin n → ℝ))))
    (u : (Fin n → ℝ) → ℝ) :
    weakWordENorm (triangularLift X P) Uo I p (fun ξ => u (basePoint ξ)) ≤
      K * weakWordENorm X Vo I p u := by
  unfold weakWordENorm
  apply sInf_le_mul_sInf hK0 hKt
  rintro r ⟨g, hg, hgm, rfl⟩
  exact ⟨eLpNorm (fun ξ => g (basePoint ξ)) p (volume.restrict (Uo : Set (Fin (n + m) → ℝ))),
    ⟨fun ξ => g (basePoint ξ), S.hasWeakWordDeriv_lift X P hXt hX I hg,
      aestronglyMeasurable_comp_basePoint Uo.isOpen.measurableSet Vo.isOpen.measurableSet S.proj hgm,
      rfl⟩, hlp g hgm⟩

/-- per nonempty word, lower inequality, when `u` has the weak
derivative `X_I u` on `Vo`: `K ‖X_I u‖_{p, Vδ} ≤ ‖X̃_I ũ‖_p`. -/
theorem le_weakWordENorm_lift (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ))) (I : List (Fin k))
    (Vδ : Opens (Fin n → ℝ)) (hδ : (Vδ : Set (Fin n → ℝ)) ⊆ (Vo : Set (Fin n → ℝ)))
    {p K : ℝ≥0∞}
    (hlp : ∀ g : (Fin n → ℝ) → ℝ, AEStronglyMeasurable g (volume.restrict (Vo : Set (Fin n → ℝ))) →
      K * eLpNorm g p (volume.restrict (Vδ : Set (Fin n → ℝ))) ≤
        eLpNorm (fun ξ => g (basePoint ξ)) p (volume.restrict (Uo : Set (Fin (n + m) → ℝ))))
    (u : (Fin n → ℝ) → ℝ) (hw : ∃ g, hasWeakWordDeriv X Vo I u g) :
    K * weakWordENorm X Vδ I p u ≤
      weakWordENorm (triangularLift X P) Uo I p (fun ξ => u (basePoint ξ)) := by
  obtain ⟨g, hg⟩ := hw
  have hgm : AEStronglyMeasurable g (volume.restrict (Vo : Set (Fin n → ℝ))) :=
    hg.2.1.aestronglyMeasurable
  have hgδ := RothschildStein.S.hasWeakWordDeriv_restrict X Vo Vδ hδ hg
  unfold weakWordENorm
  refine le_sInf ?_
  rintro r ⟨gt, hgt, hgtm, rfl⟩
  have hlift := S.hasWeakWordDeriv_lift X P hXt hX I hg
  have huniq := RothschildStein.S.hasWeakWordDeriv_unique (triangularLift X P) Uo hgt hlift
  rw [eLpNorm_congr_ae huniq]
  refine le_trans (mul_le_mul' le_rfl (sInf_le ?_)) (hlp g hgm)
  exact ⟨g, hgδ, hgδ.2.1.aestronglyMeasurable, rfl⟩

omit S in
/-- the empty word needs only measurability of `u` on `Vo`. -/
theorem le_weakWordENorm_lift_nil (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (Vδ : Opens (Fin n → ℝ)) (hδ : (Vδ : Set (Fin n → ℝ)) ⊆ (Vo : Set (Fin n → ℝ)))
    {p K : ℝ≥0∞} (hp : 1 ≤ p)
    (hlp : ∀ g : (Fin n → ℝ) → ℝ, AEStronglyMeasurable g (volume.restrict (Vo : Set (Fin n → ℝ))) →
      K * eLpNorm g p (volume.restrict (Vδ : Set (Fin n → ℝ))) ≤
        eLpNorm (fun ξ => g (basePoint ξ)) p (volume.restrict (Uo : Set (Fin (n + m) → ℝ))))
    (u : (Fin n → ℝ) → ℝ) (hu : AEStronglyMeasurable u (volume.restrict (Vo : Set (Fin n → ℝ)))) :
    K * weakWordENorm X Vδ [] p u ≤
      weakWordENorm (triangularLift X P) Uo [] p (fun ξ => u (basePoint ξ)) := by
  have huδ : AEStronglyMeasurable u (volume.restrict (Vδ : Set (Fin n → ℝ))) :=
    hu.mono_measure (Measure.restrict_mono hδ le_rfl)
  have hbound : weakWordENorm X Vδ [] p u ≤ eLpNorm u p (volume.restrict (Vδ : Set (Fin n → ℝ))) := by
    by_cases htop : eLpNorm u p (volume.restrict (Vδ : Set (Fin n → ℝ))) = ⊤
    · rw [htop]; exact le_top
    · have hmem : MemLp u p (volume.restrict (Vδ : Set (Fin n → ℝ))) :=
        lt_top_iff_ne_top.2 htop
      have hloc : LocallyIntegrableOn u (Vδ : Set (Fin n → ℝ)) volume :=
        locallyIntegrableOn_of_locallyIntegrable_restrict (hmem.locallyIntegrable hp)
      exact sInf_le ⟨u, RothschildStein.S.hasWeakWordDeriv_nil X Vδ hloc, huδ, rfl⟩
  unfold weakWordENorm at hbound ⊢
  refine le_sInf ?_
  rintro r ⟨gt, hgt, hgtm, rfl⟩
  have huniq := RothschildStein.S.hasWeakWordDeriv_unique (triangularLift X P) Uo hgt
    (RothschildStein.S.hasWeakWordDeriv_nil (triangularLift X P) Uo hgt.1)
  rw [eLpNorm_congr_ae huniq]
  exact le_trans (mul_le_mul' le_rfl hbound) (hlp u hu)

/-- Lifted norm transfer (BB (11.68)), upper inequality at the level of `W^{j,p}` (no hypothesis on `u`). -/
theorem sobolevXENorm_lift_le (w : Fin k → ℕ+) (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ))) (j : ℕ)
    {p K : ℝ≥0∞} (hK0 : K ≠ 0) (hKt : K ≠ ⊤)
    (hlp : ∀ g : (Fin n → ℝ) → ℝ, AEStronglyMeasurable g (volume.restrict (Vo : Set (Fin n → ℝ))) →
      eLpNorm (fun ξ => g (basePoint ξ)) p (volume.restrict (Uo : Set (Fin (n + m) → ℝ))) ≤
        K * eLpNorm g p (volume.restrict (Vo : Set (Fin n → ℝ))))
    (u : (Fin n → ℝ) → ℝ) :
    sobolevXENorm w (triangularLift X P) Uo j p (fun ξ => u (basePoint ξ)) ≤
      K * sobolevXENorm w X Vo j p u := by
  unfold sobolevXENorm
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun I _ => S.weakWordENorm_lift_le X P hXt hX I hK0 hKt hlp u

/-- Lifted norm transfer (BB (11.68)), lower inequality at the level of `W^{j,p}`: `u` measurable on `Vo` with
the weak derivatives `X_I u` (`I ≠ []`, `|I| ≤ j`) on `Vo`. -/
theorem le_sobolevXENorm_lift (w : Fin k → ℕ+) (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ))) (j : ℕ)
    (Vδ : Opens (Fin n → ℝ)) (hδ : (Vδ : Set (Fin n → ℝ)) ⊆ (Vo : Set (Fin n → ℝ)))
    {p K : ℝ≥0∞} (hp : 1 ≤ p)
    (hlp : ∀ g : (Fin n → ℝ) → ℝ, AEStronglyMeasurable g (volume.restrict (Vo : Set (Fin n → ℝ))) →
      K * eLpNorm g p (volume.restrict (Vδ : Set (Fin n → ℝ))) ≤
        eLpNorm (fun ξ => g (basePoint ξ)) p (volume.restrict (Uo : Set (Fin (n + m) → ℝ))))
    (u : (Fin n → ℝ) → ℝ) (hu : AEStronglyMeasurable u (volume.restrict (Vo : Set (Fin n → ℝ))))
    (hw : ∀ I ∈ wordFamily w j, I ≠ [] → ∃ g, hasWeakWordDeriv X Vo I u g) :
    K * sobolevXENorm w X Vδ j p u ≤
      sobolevXENorm w (triangularLift X P) Uo j p (fun ξ => u (basePoint ξ)) := by
  unfold sobolevXENorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun I hI => ?_
  by_cases h0 : I = []
  · subst h0
    exact le_weakWordENorm_lift_nil (Uo := Uo) (Vo := Vo) X P Vδ hδ hp hlp u hu
  · exact S.le_weakWordENorm_lift X P hXt hX I Vδ hδ hlp u (hw I hI h0)

end FiberSetting

end RothschildStein.P2

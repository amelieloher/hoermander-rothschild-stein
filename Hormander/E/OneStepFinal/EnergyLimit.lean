-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.EnergySq
public import Hormander.D.Cutoffs

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

/-- (BB Lemma 5.21, converse compactness for mollification), as an explicit hypothesis:
a tempered distribution all of whose mollifications at small scales lie in `H^s` with norm at
most `C` lies in `H^s` with norm at most `C`. -/
def MollifierConverse (N : ℕ) : Prop :=
  ∀ (s : ℝ) (T : Tempered N) (C δ₀ : ℝ), 0 < δ₀ →
    (∀ (δ : ℝ) (hδ : 0 < δ), δ < δ₀ →
      ∃ f : Hormander.A.SobolevSpace N s, f.toDistr = Hormander.A.Sδ N δ hδ T ∧ ‖f‖ ≤ C) →
    ∃ f : Hormander.A.SobolevSpace N s, f.toDistr = T ∧ ‖f‖ ≤ C

theorem cutoffDistr_energyT (θ ρ : SchwartzMap (Carrier N) ℝ)
    (hθρ : ∀ x ∈ tsupport (θ : Carrier N → ℝ), ρ x = 1) (r : ℝ) (u : Tempered N) :
    cutoffDistr ρ (Eop (energyT θ r) u) = Eop (energyT θ r) u := by
  have h : (realMultiplierOperator ρ).comp (energyT θ r) = energyT θ r := by
    apply LinearMap.ext; intro φ
    exact realMult_eq_self_of_tsupport ρ _ (fun x hx => hθρ x (tsupport_energyT_subset θ r φ hx))
  have := congrArg (fun T : Operator N => Eop T u) h
  simp only [Eop_comp (hct_realMult ρ) (hct_energyT θ r), Eop_realMult] at this
  exact this


/-- The plateau property of a cutoff relation, pointwise. -/
theorem plateau_of_precedes {f g : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes f g) :
    ∀ x ∈ tsupport f, g x = 1 := fun _ hx => subset_of_mem_nhdsSet h.2.2.2.2 hx

theorem Bdd.of_memSobolev {s : ℝ} {g : Tempered N} (v : Hormander.A.SobolevSpace N s)
    (hv : v.toDistr = g) : TemperedDistribution.MemSobolev s 2 g := by
  rw [← hv]; exact v.memSobolev_toDistr

/-- The weak-limit converse gives `X_j T^r u ∈ L²`. -/
theorem Xj_Tr_mem_L2 {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs η₁ θ ρ η₂ : SchwartzMap (Carrier N) ℝ)
    (h₁ : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (θ : Carrier N → ℝ))
    (h₂ : Hormander.D.cutoffPrecedes (θ : Carrier N → ℝ) (ρ : Carrier N → ℝ))
    (h₃ : Hormander.D.cutoffPrecedes (ρ : Carrier N → ℝ) (η₂ : Carrier N → ℝ))
    (hA6 : MollifierConverse N) (r : ℝ) (j : Fin k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Tempered N) (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = cutoffDistr η₂ u →
      b.toDistr = cutoffDistr η₂ (Eop (Hormander.C.diffusionOperator Vs cs) u) →
      ∃ v : Hormander.A.SobolevSpace N 0,
        v.toDistr = Eop ((vectorFieldOperator (Vs j.succ)).comp (energyT θ r)) u ∧
          ‖v‖ ≤ C * (‖a‖ + ‖b‖) := by
  have hθρ := plateau_of_precedes h₂
  have hθη : ∀ x ∈ tsupport (θ : Carrier N → ℝ), η₂ x = 1 :=
    plateau_of_precedes (Hormander.D.cutoffPrecedes.trans h₂ h₃)
  obtain ⟨Csq, hCsq0, hCsq⟩ := energy_sq_bound Vs cs θ η₂ hθη r
  obtain ⟨CT, hCT0, hCT⟩ := bdd_energyT θ η₂ hθη r
  obtain ⟨CQ, hCQ0, hCQ⟩ := bdd_qOp (Vs j.succ) h₁ h₂ h₃ hθη r
  obtain ⟨δ₀, hδ₀, hδ₀p⟩ := exists_mollifier_radius h₃
  refine ⟨Real.sqrt Csq + CQ, by positivity, fun u a b ha hb => ?_⟩
  set M := ‖a‖ + ‖b‖ with hM
  have hM0 : 0 ≤ M := by positivity
  refine hA6 0 _ ((Real.sqrt Csq + CQ) * M) δ₀ hδ₀ (fun δ hδ hδlt => ?_)
  obtain ⟨vrep, hvrep, -⟩ := hCT u a ha
  have hmem : TemperedDistribution.MemSobolev 0 2 (Eop (energyT θ r) u) :=
    Bdd.of_memSobolev vrep hvrep
  obtain ⟨W, hWd⟩ := exists_testFunction_Sδ ρ η₂ h₃.2.2.2.1 (Eop (energyT θ r) u) hmem
    (cutoffDistr_energyT θ ρ hθρ r u) δ hδ
    (fun x hx y hy => hδ₀p x hx y (hy.trans (by linarith)))
  have hW : (W : Tempered N) = Eop (energyA θ r δ hδ) u := by
    rw [hWd, ← Eop_mollOp]
    unfold energyA
    rw [Eop_comp (hct_mollOp δ hδ) (hct_energyT θ r)]
    rfl
  have hE := hCsq ⟨δ, hδ⟩ u a b ha hb W hW
  have hXW : sobolevNorm 0 (vectorFieldOperator (Vs j.succ) W) ≤ Real.sqrt Csq * M := by
    rw [sobolevNorm_zero_eq_sqrt]
    calc Real.sqrt _ ≤ Real.sqrt (Csq * M ^ 2) := by
          apply Real.sqrt_le_sqrt
          exact (Finset.single_le_sum (f := fun j : Fin k =>
            Hormander.C.normSq (vectorFieldOperator (Vs j.succ) W))
            (fun j _ => Hormander.C.normSq_nonneg _) (Finset.mem_univ j)).trans hE
      _ = Real.sqrt Csq * M := by
          rw [Real.sqrt_mul hCsq0, Real.sqrt_sq hM0]
  have hQ := hCQ ⟨δ, hδ⟩ u a ha
  have hsum : Hormander.A.Sδ N δ hδ (Eop ((vectorFieldOperator (Vs j.succ)).comp (energyT θ r)) u) =
      ((vectorFieldOperator (Vs j.succ) W : TestFunction N) : Tempered N) +
        Eop (qOp (Vs j.succ) θ ρ r δ hδ) u := by
    rw [← Eop_mollOp, ← ContinuousLinearMap.comp_apply,
      ← Eop_comp (hct_mollOp δ hδ) HCT.out, e6_op (Vs j.succ) θ ρ hθρ r δ hδ,
      Eop_add HCT.out HCT.out, add_apply, Eop_comp HCT.out HCT.out,
      ContinuousLinearMap.comp_apply, ← hW, Eop_test (hct_vf _)]
  have hB : Bdd 0 (Hormander.A.Sδ N δ hδ
      (Eop ((vectorFieldOperator (Vs j.succ)).comp (energyT θ r)) u))
      ((Real.sqrt Csq + CQ) * M) := by
    rw [hsum]
    refine ((Bdd.of_test 0 _).add hQ).mono ?_
    have : CQ * ‖a‖ ≤ CQ * M := by gcongr; linarith [norm_nonneg b]
    linarith
  obtain ⟨g, hg, hgn⟩ := hB
  exact ⟨g, hg, hgn⟩

end Hormander.E

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.FiniteIteration

@[expose] public section

noncomputable section

open SchwartzMap TemperedDistribution
open Hormander.B
open Hormander.Interface

namespace Hormander.E

/-- Uniform form of the finite cutoff-path iteration: a nested cutoff path
propagates localized Sobolev data inward by equal increments, with one constant `C` chosen from the
fixed frame data, the path and the orders before any distribution is given. The one-step
estimate is the hypothesis `hE2` at the fixed frame data. -/
theorem iterate_cutoff_path_uniform_of_one_step
    {k N : ℕ}
    (X : Fin (k + 1) → Carrier N → Carrier N) (c : Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (Carrier N)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s) (w : Fin N → LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (hE2 : OneStepAtFixedFrame X c hX hXc hc hcc hK hU hKU s hs w hws hw)
    {n : ℕ} {η η' : Carrier N → ℝ}
    (p : CutoffPathInside K n η η')
    {δ σ r : ℝ} (hδ : 0 < δ)
    (hδε : δ ≤ (2 : ℝ) / 4 ^ s) (hrσ : r + (n : ℝ) * δ ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : 𝓢'(Carrier N, ℂ))
        (A : Hormander.A.SobolevSpace N r)
        (B : Hormander.A.SobolevSpace N σ),
        A.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartzOuter p.precedes_outer) u →
        B.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartzOuter p.precedes_outer)
            (Hormander.hormanderOp X c u) →
        ∃ V : Hormander.A.SobolevSpace N (r + (n : ℝ) * δ),
          V.toDistr = Hormander.B.cutoffDistr
            (Hormander.B.cutoffSchwartz p.precedes_outer) u ∧
          ‖V‖ ≤ C * (‖B‖ + ‖A‖) := by
  induction p generalizing δ σ r with
  | base hηη' hη'K =>
      let r0 : ℝ := r + (↑(0 : ℕ) : ℝ) * δ
      have horder0 : r0 ≤ r := by dsimp [r0]; simp
      obtain ⟨C, hmul⟩ := realCutoff_sobolev_bound
        (Hormander.B.cutoffSchwartz hηη') r0
      refine ⟨(C : ℝ), NNReal.coe_nonneg C, ?_⟩
      intro u A B hA hB
      obtain ⟨A0, hA0, hA0norm⟩ := Hormander.A.sobolev_mono_norm horder0 A
      obtain ⟨V, hV, hVnorm⟩ := hmul A0
      have hVeq : V.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartz hηη') u := by
        calc
          V.toDistr = Hormander.B.cutoffDistr (Hormander.B.cutoffSchwartz hηη') A0.toDistr := hV
          _ = Hormander.B.cutoffDistr (Hormander.B.cutoffSchwartz hηη')
                (Hormander.B.cutoffDistr (Hormander.B.cutoffSchwartzOuter hηη') u) := by
                  rw [hA0, hA]
          _ = Hormander.B.cutoffDistr (Hormander.B.cutoffSchwartz hηη') u :=
                cutoffDistr_nested_eq hηη' u
      have hVbound : ‖V‖ ≤ (C : ℝ) * (‖B‖ + ‖A‖) := by
        have hAplus : ‖A‖ ≤ ‖B‖ + ‖A‖ := by linarith [norm_nonneg B]
        calc
          ‖V‖ ≤ (C : ℝ) * ‖A0‖ := hVnorm
          _ ≤ (C : ℝ) * ‖A‖ :=
            mul_le_mul_of_nonneg_left hA0norm (NNReal.coe_nonneg C)
          _ ≤ (C : ℝ) * (‖B‖ + ‖A‖) :=
            mul_le_mul_of_nonneg_left hAplus (NNReal.coe_nonneg C)
      exact ⟨V, hVeq, hVbound⟩
  | @insert n η ξ η' hηξ hξK prest ih =>
      let q : ℝ := r + (n : ℝ) * δ
      have hqσ : q ≤ σ := by
        dsimp [q]
        have hnext := hrσ
        push_cast at hnext
        nlinarith [hδ]
      have hqσ' : r + (n : ℝ) * δ ≤ σ := by
        dsimp [q] at hqσ
        exact hqσ
      have hstepOuter : Hormander.D.cutoffPrecedes η η' :=
        Hormander.D.cutoffPrecedes.trans hηξ prest.precedes_outer
      obtain ⟨Cprev, hCprev, hprev⟩ :=
        ih (δ := δ) (σ := σ) (r := r) hδ hδε hqσ'
      obtain ⟨Cmul, hmul⟩ := realCutoff_sobolev_bound
        (Hormander.B.cutoffSchwartz prest.precedes_outer) q
      have hηrel : Hormander.D.cutoffPrecedes
          (Hormander.B.cutoffSchwartz hηξ : Carrier N → ℝ)
          (Hormander.B.cutoffSchwartzOuter hηξ : Carrier N → ℝ) := by
        change Hormander.D.cutoffPrecedes η ξ
        exact hηξ
      have hξK' : tsupport (Hormander.B.cutoffSchwartzOuter hηξ : Carrier N → ℝ) ⊆ K := by
        change tsupport ξ ⊆ K
        exact hξK
      obtain ⟨Cstep, hstep⟩ := hE2
        (Hormander.B.cutoffSchwartz hηξ) (Hormander.B.cutoffSchwartzOuter hηξ)
        hηrel hξK' q
      refine ⟨max 0 Cstep * ((Cmul : ℝ) + Cprev),
        mul_nonneg (le_max_left 0 Cstep)
          (add_nonneg (NNReal.coe_nonneg Cmul) hCprev), ?_⟩
      intro u A B hA hB
      have hrestA : A.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartzOuter prest.precedes_outer) u := by
        calc
          A.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter hstepOuter) u := hA
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter prest.precedes_outer) u := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartzOuter_apply]
      have hrestB : B.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartzOuter prest.precedes_outer)
            (Hormander.hormanderOp X c u) := by
        calc
          B.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter hstepOuter)
                (Hormander.hormanderOp X c u) := hB
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter prest.precedes_outer)
                (Hormander.hormanderOp X c u) := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartzOuter_apply]
      obtain ⟨Aξ, hAξ, hAξnorm⟩ := hprev u A B hrestA hrestB
      obtain ⟨Bq, hBqdist, hBqnorm⟩ := Hormander.A.sobolev_mono_norm hqσ B
      obtain ⟨bξ, hbξ, hbξnorm⟩ := hmul Bq
      have hbξeq : bξ.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartzOuter hηξ) (Hormander.hormanderOp X c u) := by
        calc
          bξ.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz prest.precedes_outer) Bq.toDistr := hbξ
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz prest.precedes_outer)
                (Hormander.B.cutoffDistr
                  (Hormander.B.cutoffSchwartzOuter prest.precedes_outer)
                  (Hormander.hormanderOp X c u)) := by rw [hBqdist, hrestB]
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz prest.precedes_outer)
                (Hormander.hormanderOp X c u) :=
              cutoffDistr_nested_eq prest.precedes_outer (Hormander.hormanderOp X c u)
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter hηξ) (Hormander.hormanderOp X c u) := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartzOuter_apply, Hormander.B.cutoffSchwartz_apply]
      have hAξeq : Aξ.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartzOuter hηξ) u := by
        calc
          Aξ.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz prest.precedes_outer) u := hAξ
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter hηξ) u := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartzOuter_apply, Hormander.B.cutoffSchwartz_apply]
      obtain ⟨Veps, hVeps, hVepsnorm⟩ :=
        hstep u Aξ bξ hAξeq hbξeq
      have hVepsBound : ‖Veps‖ ≤ max 0 Cstep * (‖bξ‖ + ‖Aξ‖) := by
        apply le_trans hVepsnorm
        exact mul_le_mul_of_nonneg_right (le_max_right 0 Cstep)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
      have hgain : q + δ ≤ q + (2 : ℝ) / 4 ^ s := add_le_add_right hδε q
      obtain ⟨V, hV, hVnorm⟩ := Hormander.A.sobolev_mono_norm hgain Veps
      have hVeq : V.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartz hstepOuter) u := by
        calc
          V.toDistr = Veps.toDistr := hV
          _ = Hormander.B.cutoffDistr
                (Hormander.B.cutoffSchwartz hηξ) u := hVeps
          _ = Hormander.B.cutoffDistr
                (Hormander.B.cutoffSchwartz hstepOuter) u := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartz_apply]
      have hsum : ‖B‖ ≤ ‖B‖ + ‖A‖ := by linarith [norm_nonneg A]
      have hbξBound : ‖bξ‖ ≤ (Cmul : ℝ) * ‖B‖ :=
        le_trans hbξnorm
          (mul_le_mul_of_nonneg_left hBqnorm (NNReal.coe_nonneg Cmul))
      have hbξBound' : ‖bξ‖ ≤ (Cmul : ℝ) * (‖B‖ + ‖A‖) :=
        le_trans hbξBound (mul_le_mul_of_nonneg_left hsum (NNReal.coe_nonneg Cmul))
      have hinner : ‖bξ‖ + ‖Aξ‖ ≤ ((Cmul : ℝ) + Cprev) * (‖B‖ + ‖A‖) := by
        calc
          ‖bξ‖ + ‖Aξ‖ ≤ (Cmul : ℝ) * (‖B‖ + ‖A‖) +
              Cprev * (‖B‖ + ‖A‖) := add_le_add hbξBound' hAξnorm
          _ = ((Cmul : ℝ) + Cprev) * (‖B‖ + ‖A‖) := by ring
      have hVbound : ‖V‖ ≤
          (max 0 Cstep * ((Cmul : ℝ) + Cprev)) * (‖B‖ + ‖A‖) := by
        calc
          ‖V‖ ≤ ‖Veps‖ := hVnorm
          _ ≤ max 0 Cstep * (‖bξ‖ + ‖Aξ‖) := hVepsBound
          _ ≤ max 0 Cstep * (((Cmul : ℝ) + Cprev) * (‖B‖ + ‖A‖)) :=
              mul_le_mul_of_nonneg_left hinner (le_max_left 0 Cstep)
          _ = (max 0 Cstep * ((Cmul : ℝ) + Cprev)) * (‖B‖ + ‖A‖) := by ring
      have hVpack : ∃ V : Hormander.A.SobolevSpace N (q + δ),
          V.toDistr = Hormander.B.cutoffDistr
            (Hormander.B.cutoffSchwartz hstepOuter) u ∧
          ‖V‖ ≤ (max 0 Cstep * ((Cmul : ℝ) + Cprev)) * (‖B‖ + ‖A‖) :=
        ⟨V, hVeq, hVbound⟩
      have hstepOrder : q + δ =
          r + (↑(n + 1) : ℝ) * δ := by
        dsimp [q]
        push_cast
        ring
      rw [hstepOrder] at hVpack
      exact hVpack

/-- Uniform form of the finite iteration estimate: starting with the
negative-order input and the forcing datum of order `σ`, one constant `C`, chosen from the frame
data, the cutoffs and the orders alone, controls the full-gain localization of every admissible
`u`. The last one-step estimate supplies the full gain `2 / 4 ^ s`. -/
theorem finite_iteration_estimate_uniform_of_one_step
    {k N : ℕ}
    (X : Fin (k + 1) → Carrier N → Carrier N) (c : Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (Carrier N)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s) (w : Fin N → LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (hE2 : OneStepAtFixedFrame X c hX hXc hc hcc hK hU hKU s hs w hws hw)
    {ζ ζ' : Carrier N → ℝ}
    (hζζ' : Hormander.D.cutoffPrecedes ζ ζ')
    (hζ'K : tsupport ζ' ⊆ K)
    {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) :
    ∃ C : ℝ, ∀ (u : 𝓢'(Carrier N, ℂ))
      (A : Hormander.A.SobolevSpace N (-m))
      (B : Hormander.A.SobolevSpace N σ),
      A.toDistr = Hormander.B.cutoffDistr
        (Hormander.B.cutoffSchwartzOuter hζζ') u →
      B.toDistr = Hormander.B.cutoffDistr
        (Hormander.B.cutoffSchwartzOuter hζζ')
          (Hormander.hormanderOp X c u) →
      ∃ V : Hormander.A.SobolevSpace N (σ + (2 : ℝ) / 4 ^ s),
        V.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartz hζζ') u ∧
        ‖V‖ ≤ C * (‖B‖ + ‖A‖) := by
  have heps : 0 < (2 : ℝ) / 4 ^ s := div_pos (by norm_num) (by positivity)
  obtain ⟨n, _, hδpos, hδle, hbalance⟩ :=
    iteration_parameters hm hσ heps
  let δ : ℝ := (m + σ) / (n : ℝ)
  let q : ℝ := -m + (n : ℝ) * δ
  have hqσ : q = σ := by
    dsimp [q, δ]
    exact hbalance
  let path : CutoffPathInside K (n + 1) ζ ζ' :=
    exists_cutoff_path_inside hζζ' hζ'K (n + 1)
  cases path with
  | @insert n ζ ξ ζ' hζξ hξK prest =>
      have hstepOuter : Hormander.D.cutoffPrecedes ζ ζ' :=
        Hormander.D.cutoffPrecedes.trans hζξ prest.precedes_outer
      obtain ⟨Citer, hCiter, hiter⟩ :=
        iterate_cutoff_path_uniform_of_one_step
          X c hX hXc hc hcc hK hU hKU s hs w hws hw hE2 prest
          hδpos hδle (by dsimp [q] at hqσ; exact le_of_eq hqσ)
      obtain ⟨Cmul, hmul⟩ := realCutoff_sobolev_bound
        (Hormander.B.cutoffSchwartz prest.precedes_outer) q
      have hηrel : Hormander.D.cutoffPrecedes
          (Hormander.B.cutoffSchwartz hζξ : Carrier N → ℝ)
          (Hormander.B.cutoffSchwartzOuter hζξ : Carrier N → ℝ) := by
        change Hormander.D.cutoffPrecedes ζ ξ
        exact hζξ
      have hξK' : tsupport
          (Hormander.B.cutoffSchwartzOuter hζξ : Carrier N → ℝ) ⊆ K := by
        change tsupport ξ ⊆ K
        exact hξK
      obtain ⟨Cstep, hstep⟩ := hE2
        (Hormander.B.cutoffSchwartz hζξ)
        (Hormander.B.cutoffSchwartzOuter hζξ) hηrel hξK' q
      refine ⟨max 0 Cstep * ((Cmul : ℝ) + Citer), ?_⟩
      intro u A B hA hB
      have hArest : A.toDistr =
          Hormander.B.cutoffDistr
            (Hormander.B.cutoffSchwartzOuter prest.precedes_outer) u := by
        calc
          A.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter hstepOuter) u := hA
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter prest.precedes_outer) u := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartzOuter_apply]
      have hBrest : B.toDistr =
          Hormander.B.cutoffDistr
            (Hormander.B.cutoffSchwartzOuter prest.precedes_outer)
              (Hormander.hormanderOp X c u) := by
        calc
          B.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter hstepOuter)
                (Hormander.hormanderOp X c u) := hB
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter prest.precedes_outer)
                (Hormander.hormanderOp X c u) := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartzOuter_apply]
      obtain ⟨Aξ, hAξ, hAξnorm⟩ := hiter u A B hArest hBrest
      obtain ⟨Bq, hBqdist, hBqnorm⟩ := Hormander.A.sobolev_mono_norm
        (s₁ := q) (s₂ := σ) (le_of_eq hqσ) B
      obtain ⟨bξ, hbξ, hbξnorm⟩ := hmul Bq
      have hbξeq : bξ.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartzOuter hζξ) (Hormander.hormanderOp X c u) := by
        calc
          bξ.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz prest.precedes_outer) Bq.toDistr := hbξ
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz prest.precedes_outer)
                (Hormander.B.cutoffDistr
                  (Hormander.B.cutoffSchwartzOuter prest.precedes_outer)
                  (Hormander.hormanderOp X c u)) := by rw [hBqdist, hBrest]
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz prest.precedes_outer)
                (Hormander.hormanderOp X c u) :=
              cutoffDistr_nested_eq prest.precedes_outer (Hormander.hormanderOp X c u)
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter hζξ) (Hormander.hormanderOp X c u) := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartzOuter_apply, Hormander.B.cutoffSchwartz_apply]
      have hAξeq : Aξ.toDistr =
          Hormander.B.cutoffDistr (Hormander.B.cutoffSchwartzOuter hζξ) u := by
        calc
          Aξ.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz prest.precedes_outer) u := hAξ
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartzOuter hζξ) u := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartzOuter_apply, Hormander.B.cutoffSchwartz_apply]
      obtain ⟨V, hV, hVnorm⟩ := hstep u Aξ bξ hAξeq hbξeq
      have hVbound : ‖V‖ ≤ max 0 Cstep * (‖bξ‖ + ‖Aξ‖) := by
        apply le_trans hVnorm
        exact mul_le_mul_of_nonneg_right (le_max_right 0 Cstep)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
      have hBsum : ‖B‖ ≤ ‖B‖ + ‖A‖ := by linarith [norm_nonneg A]
      have hbξbound : ‖bξ‖ ≤ (Cmul : ℝ) * ‖B‖ :=
        le_trans hbξnorm
          (mul_le_mul_of_nonneg_left hBqnorm (NNReal.coe_nonneg Cmul))
      have hbξbound' : ‖bξ‖ ≤ (Cmul : ℝ) * (‖B‖ + ‖A‖) :=
        le_trans hbξbound
          (mul_le_mul_of_nonneg_left hBsum (NNReal.coe_nonneg Cmul))
      have hinside : ‖bξ‖ + ‖Aξ‖ ≤
          ((Cmul : ℝ) + Citer) * (‖B‖ + ‖A‖) := by
        calc
          ‖bξ‖ + ‖Aξ‖ ≤ (Cmul : ℝ) * (‖B‖ + ‖A‖) +
              Citer * (‖B‖ + ‖A‖) := add_le_add hbξbound' hAξnorm
          _ = ((Cmul : ℝ) + Citer) * (‖B‖ + ‖A‖) := by ring
      have hVeq : V.toDistr = Hormander.B.cutoffDistr
          (Hormander.B.cutoffSchwartz hζζ') u := by
        calc
          V.toDistr = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz hζξ) u := hV
          _ = Hormander.B.cutoffDistr
              (Hormander.B.cutoffSchwartz hζζ') u := by
            apply cutoffDistr_congr
            intro x
            simp [Hormander.B.cutoffSchwartz_apply]
      have hbound : ‖V‖ ≤
          (max 0 Cstep * ((Cmul : ℝ) + Citer)) * (‖B‖ + ‖A‖) := by
        calc
          ‖V‖ ≤ max 0 Cstep * (‖bξ‖ + ‖Aξ‖) := hVbound
          _ ≤ max 0 Cstep * (((Cmul : ℝ) + Citer) * (‖B‖ + ‖A‖)) :=
            mul_le_mul_of_nonneg_left hinside (le_max_left 0 Cstep)
          _ = _ := by ring
      have hresult : ∃ V : Hormander.A.SobolevSpace N (q + (2 : ℝ) / 4 ^ s),
          V.toDistr = Hormander.B.cutoffDistr
            (Hormander.B.cutoffSchwartz hζζ') u ∧
          ‖V‖ ≤ (max 0 Cstep * ((Cmul : ℝ) + Citer)) * (‖B‖ + ‖A‖) :=
        ⟨V, hVeq, hbound⟩
      rw [hqσ] at hresult
      exact hresult

end Hormander.E

end

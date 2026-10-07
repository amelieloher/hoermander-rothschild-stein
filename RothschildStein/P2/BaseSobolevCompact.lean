-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseSobolevWords
public import RothschildStein.P2.SobolevInterpolationTheorem
public import RothschildStein.P1.RepresentationSecondOrder
public import RothschildStein.P1.ContinuityTheorem
public import RothschildStein.P1.StandardFrame
public import RothschildStein.P1.GainWord

/-!
# `‖X̃_I v‖_p ≤ C (‖L̃v‖_p + ‖v‖_p)` on tests

Part of the base Sobolev estimate (BB p. 577, Thm 11.34, (11.60); used at BB pp. 585-587). The compact second-derivative estimate
of the lifted drift operator: for `1 < p < ∞` there is `Λ(p)` with
`‖X̃_I v‖_p ≤ Λ (‖L̃v‖_p + ‖v‖_p)` for every word `I` of weight two (the drift word `[0]` and the
horizontal pairs `[i + 1, j + 1]`) and every `v ∈ C_c^∞(V)` on whose support the cutoff `a` of the
representation is `1` (`CompactSecondOn`).

BB cite this estimate without derivation. It follows from the second-order representation
with `a = 1` near `supp v`,
`X̃_i X̃_j v = S_ij L̃v + ∑ₖ S_ijk X̃ₖv + S_ij0 v` (`representation_secondOrder_of`), the `L^p`
boundedness of the type-0 operators (the continuity theorem, `exists_lp_bound_standard`) and the compact Sobolev interpolation
inequality for the first-order terms; the drift word follows from
`X̃₀ v = L̃v - ∑ᵢ X̃ᵢ² v`. The statement assumes exactly the hypotheses of
`representation_secondOrder_of` (`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`,
`SignedParametrix`) and on a standard frame (the continuity theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

/-- **The compact second-derivative estimate on tests**
(BB p. 577, Thm 11.34): for every `v ∈ C_c^∞(V)` with `a = 1` on `supp v` and every word `I` of weight
two, `‖X̃_I v‖_{L^p(V)} ≤ Λ (‖L̃v‖_{L^p(V)} + ‖v‖_{L^p(V)})`, `L̃ = X̃₀ + ∑ᵢ X̃ᵢ²`
(`sumSquaresWithDrift`). -/
def CompactSecondOn {n q : ℕ} (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (V : Opens (Fin n → ℝ))
    (a : TestFunction V ℝ (⊤ : ℕ∞)) (p Λ : ℝ) : Prop :=
  ∀ v : TestFunction V ℝ (⊤ : ℕ∞), (∀ x ∈ tsupport (v : (Fin n → ℝ) → ℝ), a x = 1) →
    ∀ I ∈ wordsOfWeight w 2,
      eLpNorm (wordDerivative X I (v : (Fin n → ℝ) → ℝ)) (ENNReal.ofReal p)
          (volume.restrict (V : Set (Fin n → ℝ))) ≤
        ENNReal.ofReal Λ *
          (eLpNorm (sumSquaresWithDrift X (v : (Fin n → ℝ) → ℝ)) (ENNReal.ofReal p)
              (volume.restrict (V : Set (Fin n → ℝ))) +
            eLpNorm (v : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p)
              (volume.restrict (V : Set (Fin n → ℝ))))

/-- A finite family of reals has a nonnegative common upper bound. -/
theorem exists_nonneg_bound_fin {ι : Type*} [Finite ι] (f : ι → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, f i ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨max M 0, le_max_right _ _, fun i => (hM ⟨i, rfl⟩).trans (le_max_left _ _)⟩

variable {n q s m : ℕ} {w : Fin (q + 1) → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The compact second-derivative estimate from the
representation** (BB p. 577, Thm 11.34, (11.60)). Let `C` be a lifted drift chart, `F` a standard frame of
it and `a ∈ C_c^∞(V)` a cutoff for which the derivative representations hold (hypotheses `TypeKernelIntegrable`,
`LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, `SignedParametrix`, as in `representation_secondOrder_of`). For every
`1 < p < ∞` there is `Λ(p)` such that for `v ∈ C_c^∞(V)` with `a = 1` on `supp v` and every word `I` of
weight two (`[0]` and `[i + 1, j + 1]`),
`‖X̃_I v‖_{L^p(V)} ≤ Λ (‖L̃v‖_{L^p(V)} + ‖v‖_{L^p(V)})`. -/
theorem exists_compactSecond_of_representation
    {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
    {hQ : 2 < (C.G.homogeneousDimension : ℝ)} (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hw0 : (w 0 : ℕ) = 2)
    (B : Fin (n + m) → List (Fin (q + 1))) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w C.Xl)
    (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl) (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F C.Xl c a b) :
    ∀ p : ℝ, 1 < p → ∃ Λ : ℝ, 0 < Λ ∧ CompactSecondOn w C.Xl F.V a p Λ := by
  classical
  have hXV := hF.lifted.contDiffOn_Xl
  obtain ⟨Sml, Smlk, Sml0, -, -, -, hrep⟩ :=
    representation_secondOrder_of hXV hw0 hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
  obtain ⟨εs, hεs, hmain⟩ :=
    exists_compactInterpolation_of_representation hF hw hw0 hLeftDiff hc hc0 a hParametrix
  intro p hp
  obtain ⟨Cp, hCp, hCI⟩ := hmain p hp
  have hP1 : 1 < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := hP1.le
  choose Λ1 hΛ10 hΛ1 using fun i j : Fin q => (Sml i j).exists_lp_bound_standard hF hP1 hPtop
  choose Λ2 hΛ20 hΛ2 using fun i j k : Fin q =>
    (Smlk i j k).exists_lp_bound_standard hF hP1 hPtop
  choose Λ3 hΛ30 hΛ3 using fun i j : Fin q => (Sml0 i j).exists_lp_bound_standard hF hP1 hPtop
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_nonneg_bound_fin (fun x : Fin q × Fin q => Λ1 x.1 x.2)
  obtain ⟨M₂, hM₂0, hM₂⟩ :=
    exists_nonneg_bound_fin (fun x : Fin q × Fin q × Fin q => Λ2 x.1 x.2.1 x.2.2)
  obtain ⟨M₃, hM₃0, hM₃⟩ := exists_nonneg_bound_fin (fun x : Fin q × Fin q => Λ3 x.1 x.2)
  -- the pair estimate before interpolation
  have hpair : ∀ (i j : Fin q) (v : TestFunction F.V ℝ (⊤ : ℕ∞)),
      (∀ x ∈ tsupport (v : (Fin (n + m) → ℝ) → ℝ), a x = 1) →
      eLpNorm (wordDerivative C.Xl [i.succ, j.succ] (v : (Fin (n + m) → ℝ) → ℝ))
          (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
        ENNReal.ofReal M₁ * eLpNorm (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ))
            (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          ENNReal.ofReal M₂ * (∑ k : Fin q, eLpNorm
            (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) +
          ENNReal.ofReal M₃ * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
    intro i j v hv
    have hw1 := hrep i j v
    rw [mul_eq_self_of_eq_one_on_tsupport a v hv] at hw1
    have hcl := S.hasWeakWordDeriv_classical F.V C.Xl hXV [i.succ, j.succ]
      (v : (Fin (n + m) → ℝ) → ℝ) v.contDiff.contDiffOn
    have hae := S.hasWeakWordDeriv_unique C.Xl F.V hcl hw1
    have hLv := sumSquaresWithDriftTest_coe F.V C.Xl hXV v
    have b1 := (hΛ1 i j (sumSquaresWithDriftTest F.V C.Xl hXV v)).2
    rw [hLv] at b1
    have b2 : ∀ k : Fin q, eLpNorm ((Smlk i j k).apply
        (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ))) (ENNReal.ofReal p)
        (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
        ENNReal.ofReal (Λ2 i j k) * eLpNorm (fieldDerivative (C.Xl k.succ)
          (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := fun k =>
      (hΛ2 i j k (S.wordDerivativeTest F.V C.Xl hXV [k.succ] v)).2
    have b3 := (hΛ3 i j v).2
    have hsum : eLpNorm (fun ξ => ∑ k : Fin q, (Smlk i j k).apply
        (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) ξ) (ENNReal.ofReal p)
        (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
        ∑ k : Fin q, eLpNorm ((Smlk i j k).apply
          (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ))) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
      have e : (fun ξ => ∑ k : Fin q, (Smlk i j k).apply
          (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) ξ) =
          ∑ k : Fin q, (Smlk i j k).apply
            (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) := by
        funext ξ
        simp [Finset.sum_apply]
      rw [e]
      exact eLpNorm_sum_le hp1
    calc eLpNorm (wordDerivative C.Xl [i.succ, j.succ] (v : (Fin (n + m) → ℝ) → ℝ))
          (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
        = eLpNorm (fun ξ => (Sml i j).apply (sumSquaresWithDrift C.Xl
            (v : (Fin (n + m) → ℝ) → ℝ)) ξ +
          (∑ k : Fin q, (Smlk i j k).apply
            (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) ξ) +
          (Sml0 i j).apply (v : (Fin (n + m) → ℝ) → ℝ) ξ) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := eLpNorm_congr_ae hae
      _ ≤ eLpNorm (fun ξ => (Sml i j).apply (sumSquaresWithDrift C.Xl
            (v : (Fin (n + m) → ℝ) → ℝ)) ξ +
          (∑ k : Fin q, (Smlk i j k).apply
            (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) ξ)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          eLpNorm ((Sml0 i j).apply (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := eLpNorm_add_le hp1
      _ ≤ (eLpNorm ((Sml i j).apply (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ)))
            (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          eLpNorm (fun ξ => ∑ k : Fin q, (Smlk i j k).apply
            (fieldDerivative (C.Xl k.succ) (v : (Fin (n + m) → ℝ) → ℝ)) ξ) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) +
          eLpNorm ((Sml0 i j).apply (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
        add_le_add (eLpNorm_add_le hp1) le_rfl
      _ ≤ (ENNReal.ofReal (Λ1 i j) * eLpNorm (sumSquaresWithDrift C.Xl
            (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          ∑ k : Fin q, ENNReal.ofReal (Λ2 i j k) * eLpNorm (fieldDerivative (C.Xl k.succ)
            (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) +
          ENNReal.ofReal (Λ3 i j) * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
        add_le_add (add_le_add b1 (hsum.trans (Finset.sum_le_sum fun k _ => b2 k))) b3
      _ ≤ _ := by
        have e1 : ENNReal.ofReal (Λ1 i j) ≤ ENNReal.ofReal M₁ :=
          ENNReal.ofReal_le_ofReal (hM₁ (i, j))
        have e3 : ENNReal.ofReal (Λ3 i j) ≤ ENNReal.ofReal M₃ :=
          ENNReal.ofReal_le_ofReal (hM₃ (i, j))
        have e2 : ∑ k : Fin q, ENNReal.ofReal (Λ2 i j k) * eLpNorm (fieldDerivative (C.Xl k.succ)
            (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
            ENNReal.ofReal M₂ * ∑ k : Fin q, eLpNorm (fieldDerivative (C.Xl k.succ)
            (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun k _ => mul_le_mul'
            (ENNReal.ofReal_le_ofReal (hM₂ (i, j, k))) le_rfl
        exact add_le_add (add_le_add (mul_le_mul' e1 le_rfl) e2) (mul_le_mul' e3 le_rfl)
  -- interpolation of the first-order terms
  set ε : ℝ := min 1 (εs / 2) with hε
  have hε0 : 0 < ε := lt_min one_pos (by linarith)
  have hεs' : ε < εs := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hε1 : ε ≤ 1 := min_le_left _ _
  set Λp : ℝ := M₁ + M₂ + M₂ * (Cp / ε) + M₃ with hΛp
  have hΛp0 : 0 ≤ Λp := by
    have : 0 ≤ M₂ * (Cp / ε) := mul_nonneg hM₂0 (div_nonneg hCp.le hε0.le)
    linarith
  have hpair' : ∀ (i j : Fin q) (v : TestFunction F.V ℝ (⊤ : ℕ∞)),
      (∀ x ∈ tsupport (v : (Fin (n + m) → ℝ) → ℝ), a x = 1) →
      eLpNorm (wordDerivative C.Xl [i.succ, j.succ] (v : (Fin (n + m) → ℝ) → ℝ))
          (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
        ENNReal.ofReal Λp *
          (eLpNorm (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
            eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) := by
    intro i j v hv
    refine (hpair i j v hv).trans ?_
    have hint := hCI ε hε0 hεs' v hv
    calc _ ≤ ENNReal.ofReal M₁ * eLpNorm (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ))
            (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          ENNReal.ofReal M₂ * (ENNReal.ofReal ε * eLpNorm (sumSquaresWithDrift C.Xl
            (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
            ENNReal.ofReal (Cp / ε) * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) +
          ENNReal.ofReal M₃ * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
          add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hint)) le_rfl
      _ = (ENNReal.ofReal M₁ + ENNReal.ofReal M₂ * ENNReal.ofReal ε) *
            eLpNorm (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          (ENNReal.ofReal M₂ * ENNReal.ofReal (Cp / ε) + ENNReal.ofReal M₃) *
            eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by ring
      _ ≤ ENNReal.ofReal Λp * eLpNorm (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ))
            (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          ENNReal.ofReal Λp * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
          refine add_le_add (mul_le_mul' ?_ le_rfl) (mul_le_mul' ?_ le_rfl)
          · rw [← ENNReal.ofReal_mul hM₂0, ← ENNReal.ofReal_add hM₁0 (mul_nonneg hM₂0 hε0.le)]
            refine ENNReal.ofReal_le_ofReal ?_
            have : M₂ * ε ≤ M₂ := mul_le_of_le_one_right hM₂0 hε1
            have h2 : 0 ≤ M₂ * (Cp / ε) := mul_nonneg hM₂0 (div_nonneg hCp.le hε0.le)
            linarith
          · rw [← ENNReal.ofReal_mul hM₂0, ← ENNReal.ofReal_add (mul_nonneg hM₂0
              (div_nonneg hCp.le hε0.le)) hM₃0]
            refine ENNReal.ofReal_le_ofReal ?_
            linarith
      _ = _ := (mul_add _ _ _).symm
  -- all words of weight two
  set Λ : ℝ := ((q : ℝ) + 1) * Λp + 1 with hΛ
  have hΛ0 : 0 < Λ := by positivity
  refine ⟨Λ, hΛ0, fun v hv I hI => ?_⟩
  set NL := eLpNorm (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
    (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) with hNL
  set Nv := eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
    (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) with hNv
  have hΛpΛ : Λp ≤ Λ := by
    have : 0 ≤ (q : ℝ) * Λp := mul_nonneg (Nat.cast_nonneg q) hΛp0
    rw [hΛ]
    nlinarith
  rcases eq_zero_or_pair_of_mem_wordsOfWeight_two hw hw0 hI with rfl | ⟨i, j, rfl⟩
  · have hfun : wordDerivative C.Xl [0] (v : (Fin (n + m) → ℝ) → ℝ) =
        sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ) -
          ∑ i : Fin q, wordDerivative C.Xl [i.succ, i.succ] (v : (Fin (n + m) → ℝ) → ℝ) := by
      funext x
      simp [Finset.sum_apply, sumSquaresWithDrift, wordDerivative]
    rw [hfun]
    calc eLpNorm (sumSquaresWithDrift C.Xl (v : (Fin (n + m) → ℝ) → ℝ) -
          ∑ i : Fin q, wordDerivative C.Xl [i.succ, i.succ] (v : (Fin (n + m) → ℝ) → ℝ))
          (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
        ≤ NL + eLpNorm (∑ i : Fin q, wordDerivative C.Xl [i.succ, i.succ]
          (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := eLpNorm_sub_le hp1
      _ ≤ NL + ∑ i : Fin q, eLpNorm (wordDerivative C.Xl [i.succ, i.succ]
          (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
        add_le_add le_rfl (eLpNorm_sum_le hp1)
      _ ≤ NL + ∑ _i : Fin q, ENNReal.ofReal Λp * (NL + Nv) :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ => hpair' i i v hv)
      _ ≤ (NL + Nv) + (q : ℝ≥0∞) * (ENNReal.ofReal Λp * (NL + Nv)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact add_le_add le_self_add le_rfl
      _ = ENNReal.ofReal (1 + (q : ℝ) * Λp) * (NL + Nv) := by
        rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (Nat.cast_nonneg q) hΛp0),
          ENNReal.ofReal_one, ENNReal.ofReal_mul (Nat.cast_nonneg q), ENNReal.ofReal_natCast]
        ring
      _ ≤ ENNReal.ofReal Λ * (NL + Nv) := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [hΛ]
        nlinarith
  · exact (hpair' i j v hv).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hΛpΛ) le_rfl)

end RothschildStein.P2

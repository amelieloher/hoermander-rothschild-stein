-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SmoothOrdinaryAuxiliaryComparison
public import RothschildStein.G1.ControlledBasics

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped ENNReal Topology

namespace RothschildStein.L1

/-- A finite control distance ends in the domain: the endpoint of a
controlled curve lies in the curve's domain (BB Def 1.38, p. 21). -/
theorem mem_of_controlDistance_lt_ofReal {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {x y : Fin n → ℝ}
    {r : ℝ} (h : controlDistance Ω w X x y < ENNReal.ofReal r) : y ∈ Ω := by
  obtain ⟨_δ, _, _, γ, hγ, _, hγ1⟩ := G1.exists_controlledCurve_of_controlDistance_lt h
  exact hγ1 ▸ hγ.2.2.1 (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)

/-- Compact-uniform
auxiliary-to-ordinary comparison on a smooth bracket-generating open set: small
starred balls of radius `r` lie in the ordinary ball of radius `A r`, with the same
open set as the domain of both distances. -/
theorem exists_compact_auxiliary_ordinary_ball_inclusion {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {U K : Set (Fin n → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U) (hstep : bracketStepOn U w X s) :
    ∃ A ε : ℝ, 1 ≤ A ∧ 0 < ε ∧ ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ ε →
      {y | G4.auxiliaryDistance (s := s) U w X x y < ENNReal.ofReal r} ⊆
        {y | controlDistance U w X x y < ENNReal.ofReal (A * r)} := by
  let Q : Set (Fin n → ℝ) → Prop := fun t => ∃ A ε : ℝ, 1 ≤ A ∧ 0 < ε ∧
    ∀ x ∈ t, ∀ r : ℝ, 0 < r → r ≤ ε →
      {y | G4.auxiliaryDistance (s := s) U w X x y < ENNReal.ofReal r} ⊆
        {y | controlDistance U w X x y < ENNReal.ofReal (A * r)}
  refine hK.induction_on (p := Q) ?_ ?_ ?_ ?_
  · exact ⟨1, 1, le_rfl, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
  · rintro t t' htt' ⟨A, ε, hA, hε, h⟩
    exact ⟨A, ε, hA, hε, fun x hx => h x (htt' hx)⟩
  · rintro t t' ⟨A, ε, hA, hε, h⟩ ⟨A', ε', hA', hε', h'⟩
    refine ⟨max A A', min ε ε', le_max_of_le_left hA, lt_min hε hε', ?_⟩
    rintro x (hx | hx) r hr hrε y hy
    · exact (h x hx r hr (hrε.trans (min_le_left _ _)) hy).trans_le
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le))
    · exact (h' x hx r hr (hrε.trans (min_le_right _ _)) hy).trans_le
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le))
  · intro z hz
    obtain ⟨R, A, ε, hR, _hRU, hA, hε, hsand⟩ :=
      G4.exists_smooth_ordinary_auxiliary_ball_sandwich hn hs w hw hU X hX hstep (hKU hz)
    have hApos : 0 < A := zero_lt_one.trans_le hA
    refine ⟨K ∩ ball z (R/4), inter_mem_nhdsWithin K (ball_mem_nhds z (by positivity)),
      A, ε/A, hA, div_pos hε hApos, ?_⟩
    intro x hx r hr hrε
    have hxball : x ∈ closedBall z (R/4) := ball_subset_closedBall hx.2
    have hAr : A * r ≤ ε := by
      have := (le_div_iff₀ hApos).mp hrε
      linarith
    have hdiv : A * r / A = r := by field_simp
    have h1 := (hsand x hxball (A * r) (mul_pos hApos hr) hAr).1
    rw [hdiv] at h1
    exact h1

end RothschildStein.L1

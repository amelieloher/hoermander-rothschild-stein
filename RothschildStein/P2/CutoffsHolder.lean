-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.CutoffsTransfer
public import RothschildStein.G1.DistanceVariation
public import RothschildStein.Definitions.holderENorm

/-!
# The Hölder bound

`‖X̃_I φ‖_{C^α} ≤ C(j, α) (r - s)^{-(j+1)}` (BB pp. 579–580, Cor 11.37), from
the sup bounds for the words `I`, `i I` and the weighted gradient variation inequality of G1
(BB Thm 1.56, p. 37): with `h = d̃(ξ, η) ≤ a = r - s` the difference is at most
`C(h a^{-(j+1)} + h² a^{-(j+2)}) ≤ C h a^{-(j+1)}`, and for `h > a` at most `2 C a^{-j}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1

theorem holder_real_bound {a α h D Cg A0 A1 A2 : ℝ} {j : ℕ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hh : 0 ≤ h) (hCg : 0 ≤ Cg) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) (hD1 : D ≤ 2 * (A0 * a ^ (-(j : ℤ))))
    (hD2 : D ≤ Cg * (h * (A1 * a ^ (-((j : ℤ) + 1))) + h ^ 2 * (A2 * a ^ (-((j : ℤ) + 2))))) :
    D ≤ (Cg * (A1 + A2) + 2 * A0) * a ^ (-((j : ℤ) + 1)) * h ^ α := by
  have hP1 : 0 < a ^ (-((j : ℤ) + 1)) := zpow_pos ha0 _
  have hP2 : 0 < a ^ (-((j : ℤ) + 2)) := zpow_pos ha0 _
  have hP0 : a ^ (-(j : ℤ)) = a * a ^ (-((j : ℤ) + 1)) := by
    rw [show (-(j : ℤ)) = -((j : ℤ) + 1) + 1 by ring, zpow_add_one₀ ha0.ne', mul_comm]
  have hP1' : a ^ (-((j : ℤ) + 1)) = a * a ^ (-((j : ℤ) + 2)) := by
    rw [show (-((j : ℤ) + 1)) = -((j : ℤ) + 2) + 1 by ring, zpow_add_one₀ ha0.ne', mul_comm]
  have hK : 0 ≤ Cg * (A1 + A2) + 2 * A0 := by positivity
  rcases le_or_gt h a with hha | hha
  · have hhα : h ≤ h ^ α := by
      rcases hh.eq_or_lt with h0 | hpos
      · rw [← h0, Real.zero_rpow hα0.ne']
      · calc h = h ^ (1 : ℝ) := (Real.rpow_one h).symm
          _ ≤ h ^ α := Real.rpow_le_rpow_of_exponent_ge hpos (hha.trans ha1) hα1
    have e1 : h ^ 2 * (A2 * a ^ (-((j : ℤ) + 2))) ≤ h * (A2 * a ^ (-((j : ℤ) + 1))) := by
      rw [hP1']
      have : h * (A2 * (a * a ^ (-((j : ℤ) + 2)))) = (h * a) * (A2 * a ^ (-((j : ℤ) + 2))) := by
        ring
      rw [this]
      have : h ^ 2 = h * h := sq h
      rw [this]
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hha hh
      · positivity
    calc D ≤ Cg * (h * (A1 * a ^ (-((j : ℤ) + 1))) + h ^ 2 * (A2 * a ^ (-((j : ℤ) + 2)))) :=
          hD2
      _ ≤ Cg * (h * (A1 * a ^ (-((j : ℤ) + 1))) + h * (A2 * a ^ (-((j : ℤ) + 1)))) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl e1) hCg
      _ = Cg * (A1 + A2) * a ^ (-((j : ℤ) + 1)) * h := by ring
      _ ≤ Cg * (A1 + A2) * a ^ (-((j : ℤ) + 1)) * h ^ α :=
          mul_le_mul_of_nonneg_left hhα (by positivity)
      _ ≤ (Cg * (A1 + A2) + 2 * A0) * a ^ (-((j : ℤ) + 1)) * h ^ α := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh _)
          apply mul_le_mul_of_nonneg_right _ hP1.le
          linarith
  · have haα : a ≤ h ^ α := by
      calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
        _ ≤ a ^ α := Real.rpow_le_rpow_of_exponent_ge ha0 ha1 hα1
        _ ≤ h ^ α := Real.rpow_le_rpow ha0.le hha.le hα0.le
    calc D ≤ 2 * (A0 * a ^ (-(j : ℤ))) := hD1
      _ = 2 * A0 * (a * a ^ (-((j : ℤ) + 1))) := by rw [hP0]; ring
      _ ≤ 2 * A0 * (h ^ α * a ^ (-((j : ℤ) + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right haα hP1.le
      _ = 2 * A0 * a ^ (-((j : ℤ) + 1)) * h ^ α := by ring
      _ ≤ (Cg * (A1 + A2) + 2 * A0) * a ^ (-((j : ℤ) + 1)) * h ^ α := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh _)
          apply mul_le_mul_of_nonneg_right _ hP1.le
          have : 0 ≤ Cg * (A1 + A2) := by positivity
          linarith

/-- The Hölder norm is bounded by the sup bound and a linear-quadratic variation bound
(the case analysis `h ≤ a` / `h > a` of BB p. 580). -/
theorem holderENorm_le_of_variation {N : ℕ} (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (Vs : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) {a α Cg A0 A1 A2 : ℝ} {j : ℕ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (hCg : 0 ≤ Cg) (hA0 : 0 ≤ A0)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hsup : ∀ x, |f x| ≤ A0 * a ^ (-(j : ℤ)))
    (hvar : ∀ x ∈ Vs, ∀ y ∈ Vs, d x y < ⊤ →
      |f x - f y| ≤ Cg * ((d x y).toReal * (A1 * a ^ (-((j : ℤ) + 1))) +
        (d x y).toReal ^ 2 * (A2 * a ^ (-((j : ℤ) + 2))))) :
    holderENorm d α Vs f ≤
      ENNReal.ofReal ((A0 + (Cg * (A1 + A2) + 2 * A0)) * a ^ (-((j : ℤ) + 1))) := by
  have hP1 : 0 < a ^ (-((j : ℤ) + 1)) := zpow_pos ha0 _
  have hP0le : a ^ (-(j : ℤ)) ≤ a ^ (-((j : ℤ) + 1)) :=
    zpow_le_zpow_right_of_le_one₀ ha0 ha1 (by linarith)
  have hK : 0 ≤ Cg * (A1 + A2) + 2 * A0 := by positivity
  unfold holderENorm
  have hsupnorm : (⨆ x : Vs, ENNReal.ofReal |f x|) ≤ ENNReal.ofReal (A0 * a ^ (-((j : ℤ) + 1))) := by
    apply iSup_le
    intro x
    apply ENNReal.ofReal_le_ofReal
    exact (hsup x).trans (mul_le_mul_of_nonneg_left hP0le hA0)
  have hholder : holderSeminorm d α Vs f ≤
      ENNReal.ofReal ((Cg * (A1 + A2) + 2 * A0) * a ^ (-((j : ℤ) + 1))) := by
    apply sInf_le
    refine ⟨ENNReal.ofReal_lt_top, ?_⟩
    intro x hx y hy hd
    have hh : 0 ≤ (d x y).toReal := ENNReal.toReal_nonneg
    have hD1 : |f x - f y| ≤ 2 * (A0 * a ^ (-(j : ℤ))) := by
      calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ A0 * a ^ (-(j : ℤ)) + A0 * a ^ (-(j : ℤ)) := add_le_add (hsup x) (hsup y)
        _ = 2 * (A0 * a ^ (-(j : ℤ))) := by ring
    have hreal := holder_real_bound ha0 ha1 hα0 hα1 hh hCg hA0 hA1 hA2 hD1 (hvar x hx y hy hd)
    have hdh : d x y = ENNReal.ofReal (d x y).toReal := (ENNReal.ofReal_toReal hd.ne).symm
    rw [hdh, ENNReal.ofReal_rpow_of_nonneg hh hα0.le,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc (⨆ x : Vs, ENNReal.ofReal |f x|) + holderSeminorm d α Vs f
      ≤ ENNReal.ofReal (A0 * a ^ (-((j : ℤ) + 1))) +
          ENNReal.ofReal ((Cg * (A1 + A2) + 2 * A0) * a ^ (-((j : ℤ) + 1))) :=
        add_le_add hsupnorm hholder
    _ = ENNReal.ofReal ((A0 + (Cg * (A1 + A2) + 2 * A0)) * a ^ (-((j : ℤ) + 1))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

theorem isOpen_liftedDomain (C : LiftedChart w st Ω hΩ X x₀ m) : IsOpen C.O :=
  hΩ.preimage (continuous_pi fun j => continuous_apply (Fin.castAdd m j))

theorem contDiffOn_wordDerivative_O (C : LiftedChart w st Ω hΩ X x₀ m) (I : List (Fin k))
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wordDerivative C.Xl I f) C.O := by
  induction I with
  | nil => exact hf.contDiffOn
  | cons i I ih =>
    exact ((ih.fderiv_of_isOpen (isOpen_liftedDomain C) (m := (⊤ : ℕ∞)) (by simp))).clm_apply
      (C.lift_smooth i)

/-- The weighted gradient variation inequality for the lifted fields, in the form consumed by the
Hölder estimate: horizontal fields (weight one) are controlled by `b₁`, drift fields (weight two)
by `b₂`; the constant `Cg` depends only on the number of fields (BB Thm 1.56, p. 37). -/
def LiftedVariation (C : LiftedChart w st Ω hΩ X x₀ m) (Cg : ℝ) : Prop :=
  ∀ (v : (Fin (n + m) → ℝ) → ℝ) (b1 b2 : ℝ), ContDiffOn ℝ 1 v C.O → 0 ≤ b1 → 0 ≤ b2 →
    (∀ z ∈ C.O, ∀ i, (w i : ℕ) = 1 → |fderiv ℝ v z (C.Xl i z)| ≤ b1) →
    (∀ z ∈ C.O, ∀ i, (w i : ℕ) = 2 → |fderiv ℝ v z (C.Xl i z)| ≤ b2) →
    ∀ x y, C.dl x y < ⊤ →
      |v x - v y| ≤ Cg * ((C.dl x y).toReal * b1 + (C.dl x y).toReal ^ 2 * b2)

/-- The Hölder bound for every word, assuming the weighted variation
inequality (instantiated unconditionally for the drift and drift-free charts below). -/
theorem radialCutoff_holder_of_variation (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {Kc : Set (Fin (n + m) → ℝ)}
    (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ C.T)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hvar : LiftedVariation C Cg) (I : List (Fin k)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r → r < ρ / 2 →
      ∀ α : ℝ, 0 < α → α ≤ 1 →
      holderENorm C.dl α C.O (wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r)) ≤
        ENNReal.ofReal (CI * (r - s) ^ (-((wordWeight w I : ℤ) + 1))) := by
  choose CK hCK0 hCK using fun K : List (Fin k) =>
    radialCutoff_sup_bound C ν hν hKc hKU hρ0 hρ1 hT K
  set j := wordWeight w I with hj
  set A0 := CK I with hA0
  set A1 := ∑ i, CK (i :: I) with hA1
  have hA00 : 0 ≤ A0 := hCK0 I
  have hA10 : 0 ≤ A1 := Finset.sum_nonneg (fun i _ => hCK0 (i :: I))
  refine ⟨A0 + (Cg * (A1 + A1) + 2 * A0), by positivity, ?_⟩
  intro ξ₀ hξ₀ s r hs hsr hrρ α hα0 hα1
  have ha0 : 0 < r - s := sub_pos.2 hsr
  have ha1 : r - s ≤ 1 := by linarith
  set a := r - s with ha
  set φ := radialCutoff C ν ξ₀ s r with hφ
  have hφsm : ContDiff ℝ (⊤ : ℕ∞) φ :=
    radialCutoff_contDiff C ν hν (hKU hξ₀) hs hsr (ρ := ρ) (by linarith)
      (fun u hu => hT ξ₀ hξ₀ u hu)
  have hfsm : ContDiffOn ℝ 1 (wordDerivative C.Xl I φ) C.O :=
    (contDiffOn_wordDerivative_O C I hφsm).of_le (by simp)
  have hbound : ∀ i ξ, |wordDerivative C.Xl (i :: I) φ ξ| ≤
      CK (i :: I) * a ^ (-((w i : ℕ) + j : ℤ)) := by
    intro i ξ
    have h := hCK (i :: I) ξ₀ hξ₀ s r hs hsr hrρ ξ
    rw [wordWeight_cons] at h
    simpa [hj, Nat.cast_add] using h
  have hle : ∀ i, CK (i :: I) ≤ A1 := fun i =>
    Finset.single_le_sum (f := fun i => CK (i :: I)) (fun i _ => hCK0 (i :: I))
      (Finset.mem_univ i)
  have hP1 : 0 ≤ a ^ (-((j : ℤ) + 1)) := (zpow_pos ha0 _).le
  have hP2 : 0 ≤ a ^ (-((j : ℤ) + 2)) := (zpow_pos ha0 _).le
  refine holderENorm_le_of_variation C.dl C.O (wordDerivative C.Xl I φ) (A0 := A0) (A1 := A1)
    (A2 := A1) (j := j) ha0 ha1 hα0 hα1 hCg hA00 hA10 hA10 ?_ ?_
  · intro x
    exact hCK I ξ₀ hξ₀ s r hs hsr hrρ x
  · intro x _ y _ hxy
    refine hvar (wordDerivative C.Xl I φ) (A1 * a ^ (-((j : ℤ) + 1)))
      (A1 * a ^ (-((j : ℤ) + 2))) hfsm (by positivity) (by positivity) ?_ ?_ x y hxy
    · intro z _ i hi
      have h := hbound i z
      change |wordDerivative C.Xl (i :: I) φ z| ≤ _
      refine h.trans ?_
      rw [hi]
      have : (-((((1 : ℕ) : ℤ)) + (j : ℤ))) = -((j : ℤ) + 1) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hle i) hP1
    · intro z _ i hi
      have h := hbound i z
      change |wordDerivative C.Xl (i :: I) φ z| ≤ _
      refine h.trans ?_
      rw [hi]
      have : (-((((2 : ℕ) : ℤ)) + (j : ℤ))) = -((j : ℤ) + 2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hle i) hP2

end RothschildStein.P2

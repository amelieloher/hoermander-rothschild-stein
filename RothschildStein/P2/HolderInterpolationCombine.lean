-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# A calculus of interpolation bounds

The Hölder interpolation inequalities have the shape `A ≤ s ε S_g + c ε^{-γ} S_v` for all `0 < ε < 1`, with
`S_g = ‖L̃ v‖_∞`, `S_v = ‖v‖_∞` fixed. `InterpBound A Sg Sv s c γ` records this. It is monotone in the
constants, can be rescaled (`ε` replaced by `t ε`, `0 < t ≤ 1`), is stable under sums and under
multiplication by a nonnegative constant. The assembly of the derivative interpolation inequality
(`HolderInterpolationDerivative`) from finitely many type operators uses only this calculus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal BigOperators
namespace RothschildStein.P2

/-- `A ≤ s ε S_g + c ε^{-γ} S_v` for every `0 < ε < 1` (`s, c ≥ 0`). -/
def InterpBound (A Sg Sv : ℝ≥0∞) (s c γ : ℝ) : Prop :=
  0 ≤ s ∧ 0 ≤ c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
    A ≤ ENNReal.ofReal (s * ε) * Sg + ENNReal.ofReal (c * ε ^ (-γ)) * Sv

namespace InterpBound

variable {A B Sg Sv : ℝ≥0∞} {s c γ s' c' γ' : ℝ}

/-- A Hölder interpolation inequality in its published shape (`s = 1`). -/
theorem of_bound (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      A ≤ ENNReal.ofReal ε * Sg + ENNReal.ofReal (c * ε ^ (-γ)) * Sv) :
    InterpBound A Sg Sv 1 c γ :=
  ⟨zero_le_one, hc, fun ε hε0 hε1 => by simpa only [one_mul] using h ε hε0 hε1⟩

/-- A bound independent of `ε`. -/
theorem of_const (hc : 0 ≤ c) (h : A ≤ ENNReal.ofReal c * Sv) : InterpBound A Sg Sv 0 c 0 :=
  ⟨le_rfl, hc, fun ε _ _ => by
    simp only [zero_mul, ENNReal.ofReal_zero, neg_zero, Real.rpow_zero, mul_one, zero_add]
    exact h⟩

/-- Monotonicity in the constants and the exponent. -/
theorem mono (h : InterpBound A Sg Sv s c γ) (hs : s ≤ s') (hc : c ≤ c') (hγ : γ ≤ γ') :
    InterpBound A Sg Sv s' c' γ' := by
  obtain ⟨hs0, hc0, h⟩ := h
  refine ⟨hs0.trans hs, hc0.trans hc, fun ε hε0 hε1 => (h ε hε0 hε1).trans ?_⟩
  have h1 : s * ε ≤ s' * ε := mul_le_mul_of_nonneg_right hs hε0.le
  have h2 : c * ε ^ (-γ) ≤ c' * ε ^ (-γ') := by
    have e : ε ^ (-γ) ≤ ε ^ (-γ') :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
    exact mul_le_mul hc e (Real.rpow_nonneg hε0.le _) (hc0.trans hc)
  exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal h1) le_rfl)
    (mul_le_mul' (ENNReal.ofReal_le_ofReal h2) le_rfl)

/-- Rescaling: `ε ↦ t ε`, `0 < t ≤ 1`. -/
theorem scale (h : InterpBound A Sg Sv 1 c γ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    InterpBound A Sg Sv t (c * t ^ (-γ)) γ := by
  obtain ⟨-, hc0, h⟩ := h
  refine ⟨ht0.le, mul_nonneg hc0 (Real.rpow_nonneg ht0.le _), fun ε hε0 hε1 => ?_⟩
  have := h (t * ε) (mul_pos ht0 hε0) (by nlinarith)
  rw [Real.mul_rpow ht0.le hε0.le, one_mul] at this
  rwa [mul_assoc c]

/-- Sums. -/
theorem add (h : InterpBound A Sg Sv s c γ) (h' : InterpBound B Sg Sv s' c' γ) :
    InterpBound (A + B) Sg Sv (s + s') (c + c') γ := by
  obtain ⟨hs0, hc0, h⟩ := h
  obtain ⟨hs0', hc0', h'⟩ := h'
  refine ⟨add_nonneg hs0 hs0', add_nonneg hc0 hc0', fun ε hε0 hε1 => ?_⟩
  have e1 : ENNReal.ofReal ((s + s') * ε) =
      ENNReal.ofReal (s * ε) + ENNReal.ofReal (s' * ε) := by
    rw [add_mul, ENNReal.ofReal_add (mul_nonneg hs0 hε0.le) (mul_nonneg hs0' hε0.le)]
  have e2 : ENNReal.ofReal ((c + c') * ε ^ (-γ)) =
      ENNReal.ofReal (c * ε ^ (-γ)) + ENNReal.ofReal (c' * ε ^ (-γ)) := by
    rw [add_mul, ENNReal.ofReal_add (mul_nonneg hc0 (Real.rpow_nonneg hε0.le _))
      (mul_nonneg hc0' (Real.rpow_nonneg hε0.le _))]
  rw [e1, e2, add_mul, add_mul]
  calc A + B ≤ (ENNReal.ofReal (s * ε) * Sg + ENNReal.ofReal (c * ε ^ (-γ)) * Sv) +
        (ENNReal.ofReal (s' * ε) * Sg + ENNReal.ofReal (c' * ε ^ (-γ)) * Sv) :=
        add_le_add (h ε hε0 hε1) (h' ε hε0 hε1)
    _ = _ := by ring

/-- Multiplication by a nonnegative constant. -/
theorem const_mul (h : InterpBound A Sg Sv s c γ) {K : ℝ} (hK : 0 ≤ K) :
    InterpBound (ENNReal.ofReal K * A) Sg Sv (K * s) (K * c) γ := by
  obtain ⟨hs0, hc0, h⟩ := h
  refine ⟨mul_nonneg hK hs0, mul_nonneg hK hc0, fun ε hε0 hε1 => ?_⟩
  calc ENNReal.ofReal K * A
      ≤ ENNReal.ofReal K * (ENNReal.ofReal (s * ε) * Sg +
          ENNReal.ofReal (c * ε ^ (-γ)) * Sv) := mul_le_mul' le_rfl (h ε hε0 hε1)
    _ = ENNReal.ofReal ((K * s) * ε) * Sg + ENNReal.ofReal ((K * c) * ε ^ (-γ)) * Sv := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, mul_assoc K s ε, mul_assoc K c, ENNReal.ofReal_mul hK,
          ENNReal.ofReal_mul hK]

/-- A finite sum of interpolation bounds with a common exponent. -/
theorem sum {ι : Type*} (S : Finset ι) {A : ι → ℝ≥0∞} {s c : ι → ℝ}
    (h : ∀ i ∈ S, InterpBound (A i) Sg Sv (s i) (c i) γ) :
    InterpBound (∑ i ∈ S, A i) Sg Sv (∑ i ∈ S, s i) (∑ i ∈ S, c i) γ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨le_rfl, le_rfl, fun ε _ _ => by simp⟩
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Transport along an inequality of the quantity bounded. -/
theorem of_le {A' : ℝ≥0∞} (h : InterpBound A Sg Sv s c γ) (hA : A' ≤ A) :
    InterpBound A' Sg Sv s c γ :=
  ⟨h.1, h.2.1, fun ε hε0 hε1 => hA.trans (h.2.2 ε hε0 hε1)⟩

end InterpBound

end RothschildStein.P2

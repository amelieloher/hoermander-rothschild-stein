-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStep.Realization
public import Hormander.B.Extension.Continuity

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

/-! ### Closure of the class of operators with continuous transpose -/

theorem HasContinuousTranspose.sub' {A B : Operator N}
    (hA : HasContinuousTranspose A) (hB : HasContinuousTranspose B) :
    HasContinuousTranspose (A - B) := by
  have := hA.add (hB.smul (-1 : ℂ))
  convert this using 1
  simp [sub_eq_add_neg]

theorem HasContinuousTranspose.comm' {A B : Operator N}
    (hA : HasContinuousTranspose A) (hB : HasContinuousTranspose B) :
    HasContinuousTranspose (operatorComm A B) :=
  HasContinuousTranspose.sub' (hA.comp hB) (hB.comp hA)

/-- The transposition extension of an operator with continuous transpose (zero otherwise). -/
def Eop (T : Operator N) : Tempered N →L[ℂ] Tempered N := by
  classical
  exact if h : HasContinuousTranspose T then (ExtOp.ofTranspose T h).ext else 0

theorem Eop_eq {T : Operator N} (h : HasContinuousTranspose T) :
    Eop T = (ExtOp.ofTranspose T h).ext := by
  classical
  simp only [Eop, h, ↓reduceDIte]

theorem Eop_eq_ext (S : ExtOp N) (h : HasContinuousTranspose S.op) : Eop S.op = S.ext := by
  rw [Eop_eq h]
  exact ExtOp.ext_congr rfl

theorem Eop_comp {A B : Operator N} (hA : HasContinuousTranspose A)
    (hB : HasContinuousTranspose B) : Eop (A.comp B) = (Eop A).comp (Eop B) := by
  rw [Eop_eq (hA.comp hB), Eop_eq hA, Eop_eq hB, ← ExtOp.ext_comp]
  exact ExtOp.ext_congr rfl

theorem Eop_add {A B : Operator N} (hA : HasContinuousTranspose A)
    (hB : HasContinuousTranspose B) : Eop (A + B) = Eop A + Eop B := by
  rw [Eop_eq (hA.add hB), Eop_eq hA, Eop_eq hB, ← ExtOp.ext_add]
  exact ExtOp.ext_congr rfl

theorem Eop_smul (c : ℂ) {A : Operator N} (hA : HasContinuousTranspose A) :
    Eop (c • A) = c • Eop A := by
  rw [Eop_eq (hA.smul c), Eop_eq hA, ← ExtOp.ext_smul]
  exact ExtOp.ext_congr rfl

theorem Eop_apply {T Tt : Operator N} (hT : HasContinuousTranspose T)
    (htr : HasBilinearTranspose T Tt) (u : Tempered N) (φ : TestFunction N) :
    Eop T u φ = u (Tt φ) := by
  rw [Eop_eq hT, ExtOp.ext_apply]
  have := HasBilinearTranspose.unique (ExtOp.ofTranspose T hT).isTr htr
  rw [this]

theorem Eop_sum {ι : Type*} (I : Finset ι) (T : ι → Operator N)
    (h : ∀ i ∈ I, HasContinuousTranspose (T i)) :
    Eop (∑ i ∈ I, T i) = ∑ i ∈ I, Eop (T i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have h0 : Eop (0 : Operator N) = 0 := by
      ext u φ
      rw [Eop_apply HasContinuousTranspose.zero HasBilinearTranspose.zero]
      simp
    simpa using h0
  | insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Eop_add (h i (Finset.mem_insert_self i I))
        (HasContinuousTranspose.sum I T (fun j hj => h j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

theorem Eop_test {T : Operator N} (hT : HasContinuousTranspose T) (φ : TestFunction N) :
    Eop T (φ : Tempered N) = ((T φ : TestFunction N) : Tempered N) := by
  rw [Eop_eq hT]
  exact ExtOp.ext_test _ φ

/-! ### Bounded distributions -/

/-- `g` is (the distribution of) an element of `H^s` of norm at most `B`. -/
def Bdd (s : ℝ) (g : Tempered N) (B : ℝ) : Prop :=
  ∃ v : Hormander.A.SobolevSpace N s, v.toDistr = g ∧ ‖v‖ ≤ B

theorem Bdd.mono {s : ℝ} {g : Tempered N} {B B' : ℝ} (h : Bdd s g B) (hB : B ≤ B') :
    Bdd s g B' := by
  obtain ⟨v, hv, hn⟩ := h
  exact ⟨v, hv, hn.trans hB⟩

theorem Bdd.nonneg {s : ℝ} {g : Tempered N} {B : ℝ} (h : Bdd s g B) : 0 ≤ B := by
  obtain ⟨v, _, hn⟩ := h
  exact (norm_nonneg _).trans hn

theorem Bdd.zero (s : ℝ) {B : ℝ} (hB : 0 ≤ B) : Bdd s (0 : Tempered N) B :=
  ⟨0, rfl, by simpa using hB⟩

theorem Bdd.add {s : ℝ} {g g' : Tempered N} {B B' : ℝ} (h : Bdd s g B) (h' : Bdd s g' B') :
    Bdd s (g + g') (B + B') := by
  obtain ⟨v, hv, hn⟩ := h
  obtain ⟨v', hv', hn'⟩ := h'
  exact ⟨v + v', by rw [BesselPotentialSpace.toDistr_add, hv, hv'], (norm_add_le _ _).trans
    (add_le_add hn hn')⟩

theorem Bdd.smul {s : ℝ} {g : Tempered N} {B : ℝ} (h : Bdd s g B) (c : ℂ) :
    Bdd s (c • g) (‖c‖ * B) := by
  obtain ⟨v, hv, hn⟩ := h
  refine ⟨c • v, by rw [BesselPotentialSpace.toDistr_smul, hv], ?_⟩
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)

theorem Bdd.sum {s : ℝ} {ι : Type*} (I : Finset ι) (g : ι → Tempered N) (B : ι → ℝ)
    (h : ∀ i ∈ I, Bdd s (g i) (B i)) : Bdd s (∑ i ∈ I, g i) (∑ i ∈ I, B i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using Bdd.zero s (le_refl (0 : ℝ))
  | insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i I)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Bdd.of_test (s : ℝ) (φ : TestFunction N) : Bdd s (φ : Tempered N) (sobolevNorm s φ) :=
  ⟨Hormander.A.schwartzToSobolev s φ,
    TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr _,
    (sobolevNorm_eq_schwartzToSobolev_norm s φ).ge⟩

theorem Bdd.test_le {s : ℝ} {φ : TestFunction N} {B : ℝ} (h : Bdd s (φ : Tempered N) B) :
    sobolevNorm s φ ≤ B := by
  obtain ⟨v, hv, hn⟩ := h
  have : v = Hormander.A.schwartzToSobolev s φ := by
    apply BesselPotentialSpace.ext
    rw [hv]
    exact (TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr _).symm
  rw [sobolevNorm_eq_schwartzToSobolev_norm, ← this]
  exact hn

/-- Pairing of an `L²` distribution with a Schwartz function. -/
theorem Bdd.pairing {g : Tempered N} {B : ℝ} (h : Bdd 0 g B) (φ : TestFunction N) :
    ‖g φ‖ ≤ B * sobolevNorm 0 φ := by
  obtain ⟨v, hv, hn⟩ := h
  have h1 := abs_pairing_le_dual (σ := 0) (τ := 0) (by simp) v φ
  rw [hv, ← sobolevNorm_eq_schwartzToSobolev_norm] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right hn (sobolevNorm_nonneg _ _))

/-- Transfer of a bound on `𝓢` to `𝓢'` with a right cutoff. -/
theorem Eop_bdd {T : Operator N} (hT : HasContinuousTranspose T) {m s r' : ℝ} (hr : s + m = r')
    {C : NNReal}
    (hC : ∀ φ : TestFunction N, sobolevNorm s (T φ) ≤ (C : ℝ) * sobolevNorm r' φ)
    (ζ : SchwartzMap (Carrier N) ℝ) (hfac : T = T.comp (realMultiplierOperator ζ))
    (u : Tempered N) (w : Hormander.A.SobolevSpace N r') (hw : w.toDistr = cutoffDistr ζ u) :
    Bdd s (Eop T u) ((C : ℝ) * ‖w‖) := by
  subst hr
  have := (ExtOp.ofTranspose T hT).transfer (m := m) (r := s) (C := C) hC ζ hfac u w hw
  obtain ⟨_, v, hv, hn⟩ := this
  refine ⟨v, ?_, hn⟩
  rw [hv, Eop_eq hT]

/-- Global transfer. -/
theorem Eop_bdd_global {T : Operator N} (hT : HasContinuousTranspose T) {m s r' : ℝ}
    (hr : s + m = r') {C : NNReal}
    (hC : ∀ φ : TestFunction N, sobolevNorm s (T φ) ≤ (C : ℝ) * sobolevNorm r' φ)
    (w : Hormander.A.SobolevSpace N r') :
    Bdd s (Eop T w.toDistr) ((C : ℝ) * ‖w‖) := by
  subst hr
  obtain ⟨v, hv, hn⟩ := (ExtOp.ofTranspose T hT).transfer_global (m := m) (r := s) (C := C) hC w
  refine ⟨v, ?_, hn⟩
  rw [hv, Eop_eq hT]

/-- A bound against the cut-off input gives a global bound. -/
theorem exists_global_of_localized (ζ : SchwartzMap (Carrier N) ℝ) (s r' : ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) {ι : Type*} (T : ι → Operator N)
    (hb : ∀ i φ, sobolevNorm s (T i φ) ≤ C * sobolevNorm r' (realMultiplierOperator ζ φ)) :
    ∃ C' : NNReal, ∀ i φ, sobolevNorm s (T i φ) ≤ (C' : ℝ) * sobolevNorm r' φ := by
  have hM : HasOrder 0 (realMultiplierOperator ζ) :=
    hasOrder_multiplierOperator_zero (complexifyRealSchwartz ζ)
  obtain ⟨D, hD⟩ := hM r'
  refine ⟨C.toNNReal * D, fun i φ => ?_⟩
  calc sobolevNorm s (T i φ) ≤ C * sobolevNorm r' (realMultiplierOperator ζ φ) := hb i φ
    _ ≤ C * ((D : ℝ) * sobolevNorm (r' + 0) φ) := by
        apply mul_le_mul_of_nonneg_left (hD φ) hC0
    _ = ((C.toNNReal * D : NNReal) : ℝ) * sobolevNorm r' φ := by
        rw [add_zero, NNReal.coe_mul, Real.coe_toNNReal _ hC0]; ring

/-- Uniform transfer for a family with a common right cut-off. -/
theorem Eop_bdd_family {ι : Type*} (T : ι → Operator N) (hT : ∀ i, HasContinuousTranspose (T i))
    {m s r' : ℝ} (hr : s + m = r') (ζ : SchwartzMap (Carrier N) ℝ)
    (hfac : ∀ i, T i = (T i).comp (realMultiplierOperator ζ)) {C : ℝ}
    (hb : ∀ i φ, sobolevNorm s (T i φ) ≤ C * sobolevNorm r' (realMultiplierOperator ζ φ)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (i : ι) (u : Tempered N) (w : Hormander.A.SobolevSpace N r'),
      w.toDistr = cutoffDistr ζ u → Bdd s (Eop (T i) u) (C' * ‖w‖) := by
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hb' : ∀ i φ, sobolevNorm s (T i φ) ≤
      max C 0 * sobolevNorm r' (realMultiplierOperator ζ φ) := fun i φ =>
    (hb i φ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sobolevNorm_nonneg _ _))
  obtain ⟨C', hC'⟩ := exists_global_of_localized ζ s r' hC0 T hb'
  exact ⟨C', C'.2, fun i u w hw => Eop_bdd (hT i) hr (fun φ => hC' i φ) ζ (hfac i) u w hw⟩

/-- Uniform transfer from a `UniformOrder` bound. -/
theorem Eop_bdd_family_uniform {ι : Type*} (T : ι → Operator N)
    (hT : ∀ i, HasContinuousTranspose (T i)) {m : ℝ} (hU : UniformOrder m T) (s : ℝ) {r' : ℝ}
    (hr : s + m = r')
    (ζ : SchwartzMap (Carrier N) ℝ) (hfac : ∀ i, T i = (T i).comp (realMultiplierOperator ζ)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (i : ι) (u : Tempered N) (w : Hormander.A.SobolevSpace N r'),
      w.toDistr = cutoffDistr ζ u → Bdd s (Eop (T i) u) (C' * ‖w‖) := by
  subst hr
  obtain ⟨C, hC⟩ := hU s
  exact ⟨C, C.2, fun i u w hw => Eop_bdd (hT i) rfl (fun φ => hC i φ) ζ (hfac i) u w hw⟩

end Hormander.E

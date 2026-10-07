-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.controlDistance

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace RothschildStein.G1

/-- Increasing a positive control parameter preserves curve membership
(BB Def 1.38, p. 21). -/
theorem isControlledCurve_mono_parameter {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ ε : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ)
    (hδε : δ ≤ ε) : isControlledCurve Ω w X ε γ := by
  obtain ⟨hδ, hac, hmap, a, hmeas, ha⟩ := hγ
  refine ⟨hδ.trans_le hδε, hac, hmap, a, hmeas, ?_⟩
  filter_upwards [ha] with t ht
  exact ⟨fun i => (ht.1 i).trans (pow_le_pow_left₀ hδ.le hδε _), ht.2⟩

/-- Enlarging the domain preserves controlled curves (BB Rem 1.30, p. 18). -/
theorem isControlledCurve_mono_domain {m n : ℕ} {U Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve U w X δ γ)
    (hUΩ : U ⊆ Ω) : isControlledCurve Ω w X δ γ :=
  ⟨hγ.1, hγ.2.1, fun _t ht => hUΩ (hγ.2.2.1 ht), hγ.2.2.2⟩

/-- Constant curves have zero controls at every positive parameter
(BB Prop 1.36, p. 19). -/
theorem isControlledCurve_const {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {δ : ℝ} (hδ : 0 < δ) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    isControlledCurve Ω w X δ (fun _ => x) := by
  refine ⟨hδ, (LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval, fun _ _ => hx,
    fun _ _ => 0, fun _ => aemeasurable_const, ?_⟩
  exact Filter.Eventually.of_forall (fun t => ⟨fun i => by simp; positivity,
    by simpa using hasDerivAt_const t x⟩)

/-- Every connecting curve bounds the extended control distance
(BB Def 1.38, p. 21). -/
theorem controlDistance_le_of_curve {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ) :
    controlDistance Ω w X (γ 0) (γ 1) ≤ ENNReal.ofReal δ :=
  sInf_le ⟨δ, rfl, γ, hγ, rfl, rfl⟩

/-- A strict distance bound has a connecting curve with a strictly smaller
positive parameter (BB Def 1.38, p. 21). -/
theorem exists_controlledCurve_of_controlDistance_lt {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {x y : Fin n → ℝ} {r : ℝ}
    (h : controlDistance Ω w X x y < ENNReal.ofReal r) :
    ∃ δ, 0 < δ ∧ δ < r ∧ ∃ γ, isControlledCurve Ω w X δ γ ∧ γ 0 = x ∧ γ 1 = y := by
  obtain ⟨s, hs, hsr⟩ := (sInf_lt_iff).mp h
  obtain ⟨δ, rfl, γ, hγ, hzero, hone⟩ := hs
  refine ⟨δ, hγ.1, ?_, γ, hγ, hzero, hone⟩
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hsr).1

/-- Enlarging the domain decreases the extended control distance
(BB Rem 1.30, p. 18). -/
theorem controlDistance_mono_domain {m n : ℕ} {U Ω : Set (Fin n → ℝ)}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hUΩ : U ⊆ Ω) (x y : Fin n → ℝ) :
    controlDistance Ω w X x y ≤ controlDistance U w X x y := by
  apply sInf_le_sInf
  rintro r ⟨δ, rfl, γ, hγ, hzero, hone⟩
  exact ⟨δ, rfl, γ, isControlledCurve_mono_domain hγ hUΩ, hzero, hone⟩

/-- Distance from a point of the domain to itself is zero, before any
bracket-rank assumption (BB Prop 1.41, p. 22). -/
theorem controlDistance_self {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {x : Fin n → ℝ} (hx : x ∈ Ω) : controlDistance Ω w X x x = 0 := by
  apply le_antisymm _ bot_le
  by_contra h
  have hpos : 0 < controlDistance Ω w X x x := lt_of_not_ge h
  obtain ⟨δ, _hδ, hδpos, hlt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have hm := controlDistance_le_of_curve (isControlledCurve_const w X (ENNReal.ofReal_pos.mp hδpos) hx)
  exact (not_lt_of_ge hm) hlt

end RothschildStein.G1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MaxGauge
public import RothschildStein.Definitions.HomogeneousGroup.mul
public import RothschildStein.Definitions.HomogeneousGroup.inv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G2

/-- Homogeneous norm, with one constant for inversion and multiplication
(BB Definition 3.8, pp. 98–99). The analytic gauge axioms use the predicate. -/
structure HomogeneousNorm {N : ℕ} (G : HomogeneousGroup N) where
  toFun : (Fin N → ℝ) → ℝ
  gauge : G.IsHomogeneousGauge toFun
  c : ℝ
  one_le_c : 1 ≤ c
  inv_le : ∀ x, toFun (G.inv x) ≤ c * toFun x
  mul_le : ∀ x y, toFun (G.mul x y) ≤ c * (toFun x + toFun y)

instance HomogeneousNorm.instCoeFun {N : ℕ} {G : HomogeneousGroup N} :
    CoeFun (HomogeneousNorm G) (fun _ => (Fin N → ℝ) → ℝ) := ⟨HomogeneousNorm.toFun⟩

variable {N : ℕ} {G : HomogeneousGroup N}

/-- A symmetric norm is invariant under group inversion (BB Def 3.8, p. 99). -/
def HomogeneousNorm.Symmetric (ν : HomogeneousNorm G) : Prop := ∀ x, ν (G.inv x) = ν x

/-- Smooth homogeneous norms are smooth off the origin (BB Def 3.8, p. 99). -/
def HomogeneousNorm.Smooth (ν : HomogeneousNorm G) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ

private theorem dilation_comp (t u : ℝ) (x : Fin N → ℝ) :
    G.dilate t (G.dilate u x) = G.dilate (t * u) x := by
  ext j
  simp [HomogeneousGroup.dilate, coordinateDilation, mul_pow, mul_assoc]

private theorem dilation_one (x : Fin N → ℝ) : G.dilate 1 x = x := by
  ext j
  simp [HomogeneousGroup.dilate, coordinateDilation]

/-- Normalizing a nonzero point places it on the unit gauge sphere
(BB Prop 3.9, p. 100). -/
theorem gauge_normalize {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    ν (G.dilate (ν x)⁻¹ x) = 1 := by
  have hp : 0 < ν x := lt_of_le_of_ne (hν.2.1 x) (Ne.symm (mt (hν.2.2.1 x).mp hx))
  rw [hν.2.2.2 _ (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

/-- Positive normalization is reversible (BB Prop 3.9, p. 100). -/
theorem dilate_normalize {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    G.dilate (ν x) (G.dilate (ν x)⁻¹ x) = x := by
  have hp : ν x ≠ 0 := mt (hν.2.2.1 x).mp hx
  rw [dilation_comp, mul_inv_cancel₀ hp, dilation_one]

/-- A gauge is strictly positive away from zero (BB Prop 3.9, p. 99). -/
theorem gauge_pos {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {x : Fin N → ℝ} (hx : x ≠ 0) : 0 < ν x :=
  lt_of_le_of_ne (hν.2.1 x) (Ne.symm (mt (hν.2.2.1 x).mp hx))

/-- The max-gauge unit sphere is compact (BB Prop 3.9, p. 99). -/
theorem isCompact_max_unit (G : HomogeneousGroup N) :
    IsCompact {x : Fin N → ℝ | rsGauge G.weight G.weight_pos x = 1} := by
  apply (isCompact_gauge_sublevel G 1).of_isClosed_subset
    (isClosed_eq (continuous_gauge G) continuous_const)
  intro x hx
  exact le_of_eq hx

/-- Every continuous homogeneous gauge is globally comparable to the
coordinate max gauge (BB Theorem 3.12, pp. 101–102). -/
theorem gauge_equivalent_max {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x,
      a * rsGauge G.weight G.weight_pos x ≤ ν x ∧
      ν x ≤ b * rsGauge G.weight G.weight_pos x := by
  let μ := rsGauge G.weight G.weight_pos
  have hμ := isHomogeneousGauge_max G
  have hne : ({x : Fin N → ℝ | μ x = 1} : Set _).Nonempty := by
    let x : Fin N → ℝ := Pi.single ⟨0, G.dimension_pos⟩ 1
    have hx : x ≠ 0 := by
      intro h
      have := congrFun h ⟨0, G.dimension_pos⟩
      simp [x] at this
    exact ⟨G.dilate (μ x)⁻¹ x, gauge_normalize hμ hx⟩
  obtain ⟨xmin, hxmin, hmin⟩ := (isCompact_max_unit G).exists_isMinOn hne hν.1.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := (isCompact_max_unit G).exists_isMaxOn hne hν.1.continuousOn
  have hxmin0 : xmin ≠ 0 := by
    intro h
    have hz := (hμ.2.2.1 0).mpr rfl
    simp only [mem_ofPred_eq] at hxmin
    rw [h, hz] at hxmin
    norm_num at hxmin
  have hxmax0 : xmax ≠ 0 := by
    intro h
    have hz := (hμ.2.2.1 0).mpr rfl
    simp only [mem_ofPred_eq] at hxmax
    rw [h, hz] at hxmax
    norm_num at hxmax
  refine ⟨ν xmin, ν xmax, gauge_pos hν hxmin0, gauge_pos hν hxmax0, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    rw [(hν.2.2.1 0).mpr rfl, (hμ.2.2.1 0).mpr rfl]
    simp
  · have hp := gauge_pos hμ hx
    have hunit := gauge_normalize hμ hx
    have hlo := hmin hunit
    have hhi := hmax hunit
    have heq : ν x = μ x * ν (G.dilate (μ x)⁻¹ x) := by
      conv_lhs => rw [← dilate_normalize hμ hx]
      rw [hν.2.2.2 _ hp]
    constructor
    · calc
        ν xmin * μ x = μ x * ν xmin := mul_comm _ _
        _ ≤ μ x * ν (G.dilate (μ x)⁻¹ x) := mul_le_mul_of_nonneg_left hlo hp.le
        _ = ν x := heq.symm
    · calc
        ν x = μ x * ν (G.dilate (μ x)⁻¹ x) := heq
        _ ≤ μ x * ν xmax := mul_le_mul_of_nonneg_left hhi hp.le
        _ = ν xmax * μ x := mul_comm _ _

/-- Every homogeneous gauge has compact sublevels (BB Prop 3.9, pp. 99–100). -/
theorem isCompact_gauge_le {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (r : ℝ) : IsCompact {x : Fin N → ℝ | ν x ≤ r} := by
  obtain ⟨a, _, ha, _, hbound⟩ := gauge_equivalent_max hν
  apply (isCompact_gauge_sublevel G (r / a)).of_isClosed_subset
    (isClosed_le hν.1 continuous_const)
  intro x hx
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  exact (hbound x).1.trans hx

/-- Any two homogeneous gauges are equivalent (BB Thm 3.12, pp. 101–102). -/
theorem gauges_equivalent {ν μ : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hμ : G.IsHomogeneousGauge μ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ν x ≤ μ x ∧ μ x ≤ b * ν x := by
  obtain ⟨aν, bν, haν, hbν, hνb⟩ := gauge_equivalent_max hν
  obtain ⟨aμ, bμ, haμ, hbμ, hμb⟩ := gauge_equivalent_max hμ
  refine ⟨aμ / bν, bμ / aν, div_pos haμ hbν, div_pos hbμ haν, ?_⟩
  intro x
  constructor
  · calc
      aμ / bν * ν x ≤ aμ / bν * (bν * rsGauge G.weight G.weight_pos x) :=
        mul_le_mul_of_nonneg_left (hνb x).2 (div_pos haμ hbν).le
      _ = aμ * rsGauge G.weight G.weight_pos x := by field_simp
      _ ≤ μ x := (hμb x).1
  · have h := (hνb x).1
    have hn : rsGauge G.weight G.weight_pos x ≤ ν x / aν := by
      exact (le_div_iff₀ haν).mpr (by simpa [mul_comm] using h)
    calc
      μ x ≤ bμ * rsGauge G.weight G.weight_pos x := (hμb x).2
      _ ≤ bμ * (ν x / aν) := mul_le_mul_of_nonneg_left hn hbμ.le
      _ = bμ / aν * ν x := by ring

end RothschildStein.G2

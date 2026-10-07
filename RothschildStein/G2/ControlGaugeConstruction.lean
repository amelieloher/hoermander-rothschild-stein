-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlEuclideanContinuity
public import RothschildStein.G2.ControlMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped Topology ENNReal
namespace RothschildStein.G2

/-- The control gauge is the real value of the actual weighted control distance from the identity (BB Thm 3.54, pp. 125–127). -/
def controlDistanceGauge {N m : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) : ℝ :=
  (controlDistance univ w X x 0).toReal

/-- The full local
comparison implies genuine finiteness on the connected group carrier
(BB Thm 3.54, pp. 125–127; G1 Thm 1.45, p. 34). -/
theorem controlDistance_group_ne_top_of_local_comparison {N m s : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hs : 0 < s) (hcomparison : G1.LocalControlComparison univ w X s)
    (x y : Fin N → ℝ) : controlDistance univ w X x y ≠ ∞ :=
  G1.controlDistance_ne_top_of_local_comparison isOpen_univ isPreconnected_univ
    w X hs hcomparison (mem_univ x) (mem_univ y)

/-- Euclidean continuity of the
control gauge follows from joint control-distance continuity and proved
finiteness. Continuity is not assumed as a gauge premise
(BB Thm 3.54, p. 126). -/
theorem continuous_controlDistanceGauge_of_local_comparison {N m s : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, Continuous (X i)) (hs : 0 < s)
    (hcomparison : G1.LocalControlComparison univ w X s) :
    Continuous (controlDistanceGauge w X) := by
  have hpair : Continuous (fun x : Fin N → ℝ =>
      ((⟨x,mem_univ x⟩ : (univ : Set (Fin N → ℝ))),
        (⟨0,mem_univ 0⟩ : (univ : Set (Fin N → ℝ))))) :=
    (continuous_id.subtype_mk (fun x => mem_univ x)).prodMk continuous_const
  have hd := (G1.continuous_controlDistance_of_local_comparison isOpen_univ w X
    (fun i => (hX i).continuousOn) hs hcomparison).comp hpair
  have hd' : Continuous (fun x : Fin N → ℝ => controlDistance univ w X x 0) := hd
  exact ENNReal.continuousOn_toReal.comp_continuous hd'
    (fun x => controlDistance_group_ne_top_of_local_comparison w X hs hcomparison x 0)

/-- Positivity, separation,
continuity and degree-one homogeneity of the actual control gauge
(BB Thm 3.54, pp. 125–127; weighted transport (3.37)). -/
theorem isHomogeneousGauge_controlDistance_of_local_comparison {N m s : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, Continuous (X i))
    (hhom : ∀ i, IsHomogeneousField G (X i) (w i : ℕ))
    (hs : 0 < s) (hcomparison : G1.LocalControlComparison univ w X s) :
    G.IsHomogeneousGauge (controlDistanceGauge w X) := by
  refine ⟨continuous_controlDistanceGauge_of_local_comparison w X hX hs hcomparison,
    fun x => ENNReal.toReal_nonneg,?_,?_⟩
  · intro x
    constructor
    · intro hz
      have hf := controlDistance_group_ne_top_of_local_comparison w X hs hcomparison x 0
      have he : controlDistance univ w X x 0 = 0 := by
        rw [← ENNReal.ofReal_toReal hf]
        change ENNReal.ofReal (controlDistanceGauge w X x) = 0
        rw [hz,ENNReal.ofReal_zero]
      exact (G1.controlDistance_eq_zero_iff isOpen_univ w X
        (fun i => (hX i).continuousOn) (mem_univ x)).mp he
    · intro hz
      subst x
      simp [controlDistanceGauge,G1.controlDistance_self w X (mem_univ (0 : Fin N → ℝ))]
  · intro t ht x
    have he := controlDistance_homogeneous G w X hhom t ht x 0
    rw [dilate_zero G] at he
    change (controlDistance univ w X (G.dilate t x) 0).toReal =
      t * (controlDistance univ w X x 0).toReal
    rw [he,ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le]

end RothschildStein.G2

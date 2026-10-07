-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.NormConstruction
public import RothschildStein.G2.Quasidistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Gauge quasidistance is homogeneous (BB Prop 3.16, p. 103). -/
theorem gaugeDistance_dilate {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (t : ℝ) (ht : 0 < t) (x y : Fin N → ℝ) :
    gaugeDistance G ν (G.dilate t x) (G.dilate t y) = t * gaugeDistance G ν x y :=
  gaugeDistance_dilate_of_groupIdentities G (fun _ ht x => inv_dilate G ht x) hν t ht x y

/-- Gauge quasidistance is left invariant (BB Proposition 3.16, p. 103). -/
theorem gaugeDistance_leftInvariant (ν : (Fin N → ℝ) → ℝ) (x y z : Fin N → ℝ) :
    gaugeDistance G ν (G.mul z x) (G.mul z y) = gaugeDistance G ν x y :=
  gaugeDistance_leftInvariant_of_groupIdentities G (inv_product G) ν x y z

/-- An inversion invariant homogeneous norm gives a symmetric
quasidistance (BB Prop 3.16, p. 103). -/
theorem gaugeDistance_symmetric (ν : HomogeneousNorm G) (hν : ν.Symmetric) (x y : Fin N → ℝ) :
    gaugeDistance G ν y x = gaugeDistance G ν x y :=
  gaugeDistance_symmetric_of_groupIdentities G (inv_inv G) (inv_product G) ν hν x y

/-- The common-multiple smooth norm is symmetric under inversion (BB pp. 100–101; Remark 11.35, p. 578). -/
theorem smoothNorm_symmetric (hi : HasNegInverse G) : (smoothNorm G).Symmetric := by
  intro x
  change smoothGauge G (G.inv x) = smoothGauge G x
  rw [hi x]
  exact smoothGauge_neg G x

end RothschildStein.G2

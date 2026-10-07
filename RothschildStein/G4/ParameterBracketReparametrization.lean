-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.JointAdjointJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Reparametrizing stationary coefficients commutes exactly with
every spatial adjoint iteration. No parameter derivatives enter this
identity (BB Lemma 9.48, pp. 441–443). -/
theorem spatialBracketFamily_iterate_parameter_reparametrization {P Q E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Q → P) (Z Y : P × E → E) (p : Q × E) (k : ℕ) :
    ((spatialBracketFamily (fun q : Q × E => Z (a q.1, q.2)))^[k]
      (fun q : Q × E => Y (a q.1, q.2))) p =
      ((spatialBracketFamily Z)^[k] Y) (a p.1, p.2) := by
  have h₁ := congrFun (spatialBracketFamily_iterate_slice
    (fun q : Q × E => Z (a q.1, q.2)) (fun q : Q × E => Y (a q.1, q.2)) p.1 k) p.2
  have h₂ := congrFun (spatialBracketFamily_iterate_slice Z Y (a p.1) k) p.2
  simpa only [Prod.mk.eta] using h₁.trans h₂.symm

end RothschildStein.G4

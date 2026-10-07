-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FiniteGeneratorCosts
public import RothschildStein.G1.OpenOrbits
public import RothschildStein.G1.ControlConstancy

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- Finite generator connectivity on a connected domain follows from
local connectivity in every smaller open neighborhood
(BB Theorem 1.45, p. 34). -/
theorem finite_generator_connectivity_of_local_connectivity {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hlocal : ∀ x ∈ Ω, ∀ W : Set (Fin n → ℝ), IsOpen W → x ∈ W → W ⊆ Ω →
      ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
        ∀ a ∈ U, ∀ b ∈ U, FiniteGeneratorPath W X a b)
    {x y : Fin n → ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) : FiniteGeneratorPath Ω X x y := by
  apply relation_universal_of_local_reachability hconn (FiniteGeneratorPath Ω X)
    (fun x _ => Relation.EqvGen.refl x)
    (fun {x y} h => Relation.EqvGen.symm x y h)
    (fun {x y z} h₁ h₂ => Relation.EqvGen.trans x y z h₁ h₂) ?_ hx hy
  intro z hz
  obtain ⟨U, hU, hzU, hUΩ, hpaths⟩ := hlocal z hz Ω hΩ hz Subset.rfl
  exact ⟨U, hU, hzU, hUΩ, fun v hv => hpaths z hzU v hv⟩

end RothschildStein.G1

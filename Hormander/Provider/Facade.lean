-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.BasisVec
public import Hormander.Interface.LieWord
public import Hormander.Interface.LieWordEval
public import Hormander.Interface.LieAlgebraSpansOn
public import Hormander.Interface.EuclideanDivergence
public import Hormander.Interface.HormanderAdjointTest
public import Hormander.Interface.HasWeakHormanderEquation
public import Hormander.F.Assembly.Main
public import Hormander.F.LocalizedForcing
public import Hormander.Provider.LocalRegularity

/-!
# Smooth representative for the Hörmander equation

The theorem follows from the local regularity estimate and the localized forcing identity.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open Hormander.Interface

namespace Hormander.Provider

/-- Hörmander's hypoellipticity theorem (1967, Theorem 1.1) for `X₀ + Σ Xᵢ² + c`:
a locally integrable weak solution agrees almost everywhere with a smooth function. -/
theorem exists_smooth_aeRepresentative
    {k N : ℕ} {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c g u : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hspan : LieAlgebraSpansOn Ω X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hEq : HasWeakHormanderEquation Ω X c g u) :
    ∃ f : (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f :=
  Hormander.F.exists_smooth_aeRepresentative_of_E4_forcing hΩ X c g u hX hspan hc hEq
    (fun {_k _N} X c hX hXc hc hcc {_K _U} hK hU hKU w hw {_ζ _ζ'} hζ hζ' hζζ' hζ'K u f hf {_m} hm =>
      Hormander.Provider.forall_memSobolev_of_localized X c hX hXc hc hcc hK hU hKU w hw
        hζ hζ' hζζ' hζ'K u f hf hm)
    (fun hN x₀ P =>
      Hormander.F.localized_forcing_of_weak_equation hN hΩ X c g u hX hc hEq x₀ P)

end Hormander.Provider

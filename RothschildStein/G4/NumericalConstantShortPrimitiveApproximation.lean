-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.NumericalBufferedPrimitiveControlApproximation
public import RothschildStein.G4.ConstantShortFiniteLieEndpoint
public import RothschildStein.G4.ControlTopology

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.G4
open G3 G1

/-- Every genuine small constant short-control curve in a
common compact buffer has a primitive reachable endpoint with ordinary
cost O(δ) and Euclidean error O(δ^(s+1)). Both conclusions come from
actual flows and the retained formal target, not from an approximation
premise (BB pp. 459–460). -/
theorem exists_numerical_constant_short_primitive_approximation {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (i₀ : Fin m) {r B R : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    : ∃ C η M : ℝ, 0 < C ∧ 0 < η ∧ η ≤ 1 ∧ 0 < M ∧
      ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → ∀ z : Fin n → ℝ,
      (centreBuffer K r : Set (Fin n → ℝ)) ⊆ closedBall z R →
      closedBall z R ⊆ Ω →
      ∀ X : Fin m → (Fin n → ℝ) → (Fin n → ℝ),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
      CoordinateMultiIndexBudget (centreBuffer K r) X (4 * (s + 1)^3) B →
      ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ a : Fin (Fintype.card (ShortWord w s)) → ℝ,
        (∀ j, |a j| ≤ δ ^ (shortWeight w (shortIndex w j) : ℕ)) →
      ∀ γ : ℝ → (Fin n → ℝ), AbsolutelyContinuousOnInterval γ 0 1 →
        MapsTo γ (Icc 0 1) (closedBall z R) →
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          HasDerivAt γ (∑ j, a j • shortField w X (shortIndex w j) (γ t)) t) →
        γ 0 ∈ K → ∃ y ∈ Ω,
          controlDistance Ω w X (γ 0) y ≤ ENNReal.ofReal (C * δ) ∧
          ‖y - γ 1‖ ≤ M * δ ^ (s + 1) := by
  obtain ⟨A,η,M,κ,σ,hA,hη,hηone,hM,hκ,hσ,hprovider⟩ :=
    exists_numerical_buffered_primitive_control_approximation (n := n) D hs hw i₀ hr hB
  let C := (enumeratedPrimitiveArcCount m s w : ℝ) * A + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, η, M, hC, hη, hηone, hM, ?_⟩
  intro Ω K hΩ z hbuffer hRΩ X hX hjets
  obtain ⟨Φ,hΦ,hODE,happrox⟩ := hprovider Ω K (hbuffer.trans hRΩ) X
    (fun i => (hX i).mono (hbuffer.trans hRΩ)) hjets
  intro δ hδ hδη a ha γ hac hγ hd hx
  let c := shortWordCoefficients (fun I => a (Fintype.equivFin (ShortWord w s) I))
  have hc : ∀ I ∈ correctionWordEnumeration m s w s, |c I| ≤ δ ^ wordWeight w I :=
    shortWordCoefficients_coordinate_weighted_bound a δ ha
  obtain ⟨S, _hlen, hcoords, hS⟩ := happrox δ hδ hδη c hc
  have hxU : γ 0 ∈ centreBuffer K (r/2) :=
    mem_centreBuffer_iff.mpr ⟨γ 0, hx, mem_ball_self (by positivity)⟩
  have he := constant_short_curve_finiteLie_endpoint D hΩ X hX a hRΩ γ hac hγ hd
    Φ hΦ hcoords hxU (hODE _ hcoords _ hxU).1
    (fun t ht => ⟨hbuffer ((hODE _ hcoords _ hxU).2 t ht).1,
      ((hODE _ hcoords _ hxU).2 t ht).2⟩)
  let y := runTimedPrimitiveSchedule (primitiveFlowFromLieFamily D Φ κ) S (γ 0)
  have hcost : controlDistance Ω w X (γ 0) y ≤ ENNReal.ofReal (C * δ) :=
    (hS _ hx).1.trans (ENNReal.ofReal_le_ofReal (by
      dsimp [C]
      nlinarith [mul_pos hA hδ]))
  have hyΩ : y ∈ Ω := by
    apply controlBall_subset_domain Ω w X (γ 0) (C * δ + 1)
    exact hcost.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < C * δ + 1)).mpr
      (by linarith))
  refine ⟨y, hyΩ, hcost, ?_⟩
  rw [he]
  exact (hS _ hx).2

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.UniformPrimitiveWordApproximation
public import RothschildStein.G4.BoundedTimedPrimitiveControlCost

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- The buffered construction gives a primitive approximation
with both its ordinary control cost and its Euclidean endpoint error.
The time threshold is shrunk to retain every primitive-flow domain
(BB pp. 459–460). -/
theorem exists_buffered_primitive_control_approximation {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (i₀ : Fin m) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {Ω K : Set (Fin n → ℝ)} (hbuffer : (centreBuffer K r : Set (Fin n → ℝ)) ⊆ Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (centreBuffer K r))
    (hjets : CoordinateMultiIndexBudget (centreBuffer K r) X (4 * (s + 1)^3) B) :
    ∃ A η M κ σ : ℝ, 0 < A ∧ 0 < η ∧ η ≤ 1 ∧ 0 < M ∧ 0 < κ ∧ 0 < σ ∧
      ∃ Φ : (((Fin (freeDimension m s w) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Φ
          ((ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin n → ℝ))) ×ˢ Ioo (-2) 2) ∧
        (∀ f : formalSpan m s w, D.basis.equivFun f ∈ ball 0 σ →
          ∀ x ∈ centreBuffer K (r/2), Φ ((D.basis.equivFun f,x),0) = x ∧
            ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun f,x),t) ∈ centreBuffer K r ∧
              HasDerivAt (fun v => Φ ((D.basis.equivFun f,x),v))
                (finiteLieField D X f (Φ ((D.basis.equivFun f,x),t))) t) ∧
        ∀ δ : ℝ, 0 < δ → δ < η → ∀ c : List (Fin m) → ℝ,
          (∀ I ∈ correctionWordEnumeration m s w s, |c I| ≤ δ^wordWeight w I) →
          ∃ S : List (Fin m × ℝ), S.length = enumeratedPrimitiveArcCount m s w ∧
            D.basis.equivFun (normalizedWordTarget c) ∈ ball 0 σ ∧
            ∀ x ∈ K,
              controlDistance Ω w X x (runTimedPrimitiveSchedule (primitiveFlowFromLieFamily D Φ κ) S x) ≤
                ENNReal.ofReal ((enumeratedPrimitiveArcCount m s w : ℝ) * A * δ) ∧
              ‖runTimedPrimitiveSchedule (primitiveFlowFromLieFamily D Φ κ) S x -
                finiteLieTimeOneMap Φ (D.basis.equivFun (normalizedWordTarget c),x)‖ ≤ M * δ^(s+1) := by
  obtain ⟨A, η, M, κ, σ, hA, hη, hηone, hM, hκ, hσ, hprovider⟩ :=
    exists_uniform_primitive_word_approximation (N := n) D hs hw i₀ hr hB
  obtain ⟨Φ, hΦ, hODE, hΨ, hΨODE, happrox⟩ := hprovider K X hX hjets
  let L := max 1 A
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  let η' := min η (min 1 (κ / (2 * L)))
  have hη' : 0 < η' := lt_min hη (lt_min zero_lt_one (div_pos hκ (by positivity)))
  have hUΩ : (centreBuffer K (r/2) : Set (Fin n → ℝ)) ⊆ Ω := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := mem_centreBuffer_iff.mp hy
    exact hbuffer (mem_centreBuffer_iff.mpr ⟨x, hx,
      (ball_subset_ball (by linarith : r/2 ≤ r)) hyx⟩)
  refine ⟨L, η', M, κ, σ, hL, hη', (min_le_right _ _).trans (min_le_left _ _),
    hM, hκ, hσ, Φ, hΦ, hODE, ?_⟩
  intro δ hδ hδη c hc
  have hδη₀ : δ < η := hδη.trans_le (min_le_left _ _)
  have hδone : δ ≤ 1 := (hδη.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδκ : L * δ < κ := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * L)).mp
      (hδη.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith [mul_pos hL hδ]
  obtain ⟨S, hlen, htimes, hcoords, he⟩ := happrox δ hδ hδη₀ c hc
  have ht : ∀ b ∈ S, |b.2| < κ := by
    intro b hb
    have hp : δ ^ (w b.1 : ℕ) ≤ δ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hδ.le hδone (w b.1).pos
    exact ((htimes b hb).trans ((mul_le_mul_of_nonneg_left hp hA.le).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 A) hδ.le))).trans_lt hδκ
  refine ⟨S, hlen, hcoords, ?_⟩
  intro x hx
  have hxU : x ∈ centreBuffer K (r/2) :=
    mem_centreBuffer_iff.mpr ⟨x, hx, mem_ball_self (by positivity)⟩
  have hcost := controlDistance_bounded_timed_primitive_schedule hUΩ w X hδ
    (primitiveFlowFromLieFamily D Φ κ) hΨ (fun i y hy =>
      ⟨(hΨODE i y hy).1, fun v hv => ⟨((hΨODE i y hy).2 v hv).2,
        hbuffer ((hΨODE i y hy).2 v hv).1⟩⟩) S ht htimes hxU (he x hx).1
  exact ⟨by simpa only [hlen, L] using hcost, (he x hx).2⟩

end RothschildStein.G4

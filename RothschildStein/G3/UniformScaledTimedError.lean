-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformRetainedListError
public import RothschildStein.G3.ScaledTimedRetainedLists
public import RothschildStein.G3.TimedCoefficientBudget
public import RothschildStein.G3.NumericalPrimitiveRescaling
public import RothschildStein.G3.PrimitiveFlowDisplacement
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- Bounded normalized real primitive times have a uniform actual approximation
with polynomial weighted dilation and whole-arc buffer containment. -/
theorem exists_uniform_scaledTimed_BCH_error {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) (hp : ∀ i, (p i : ℕ) ≤ s)
    {r B A R : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hA : 0 ≤ A) (hR : 0 ≤ R) (L : ℕ) :
    ∃ η M κ σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < M ∧ 0 < κ ∧ 0 < σ ∧
      ∀ (K : Set (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (centreBuffer K r)) →
        (∀ x ∈ centreBuffer K r, ∀ i j, j ≤ 3*s+2 → ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B) →
        ∃ Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) Φ
            ((ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) ×ˢ Ioo (-2) 2) ∧
          (∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
            ∀ x ∈ centreBuffer K (r/2), Φ ((D.basis.equivFun f,x),0) = x ∧
              ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun f,x),t) ∈ centreBuffer K r ∧
                HasDerivAt (fun v => Φ ((D.basis.equivFun f,x),v))
                  (finiteLieField D X f (Φ ((D.basis.equivFun f,x),t))) t) ∧
          (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (primitiveFlowFromLieFamily D Φ κ i)
            ((centreBuffer K (r/2) : Set (Fin N → ℝ)) ×ˢ Ioo (-κ) κ)) ∧
          (∀ i x, x ∈ centreBuffer K (r/2) → primitiveFlowFromLieFamily D Φ κ i (x,0) = x ∧
            ∀ v ∈ Ioo (-κ) κ, primitiveFlowFromLieFamily D Φ κ i (x,v) ∈ centreBuffer K r ∧
              HasDerivAt (fun w => primitiveFlowFromLieFamily D Φ κ i (x,w))
                (X i (primitiveFlowFromLieFamily D Φ κ i (x,v))) v) ∧
          ∀ S : List (Fin a × ℝ), S.length ≤ L → (∀ b ∈ S, |b.2| ≤ A) →
            ‖retainedLieListProduct (S.map (timedPrimitiveLieInput (s := s) (p := p)))‖ ≤ R →
            ∀ x ∈ K, ∀ t : ℝ, |t| < η →
              TimedScheduleInside (primitiveFlowFromLieFamily D Φ κ) (centreBuffer K (r/2))
                (scaleTimedPrimitiveSchedule p t S) x ∧
              ‖runTimedPrimitiveSchedule (primitiveFlowFromLieFamily D Φ κ)
                  (scaleTimedPrimitiveSchedule p t S) x - finiteLieTimeOneMap Φ
                  (dilatedInputCoordinates D (retainedLieListProduct (S.map (timedPrimitiveLieInput (s := s) (p := p)))) t,x)‖ ≤
                M*|t| ^(s+1) := by
  obtain ⟨T,hT,hprimitive,htarget⟩ := exists_timedPrimitive_coefficient_budget D hA hR
  obtain ⟨ε,M,σ,hε,hM,hσ,hflow⟩ := exists_uniform_retainedLie_list_BCH_error
    (N := N) D hs hr hB hT.le L
  obtain ⟨κ,hκ,_,hcoeff⟩ := exists_primitive_rescaling_radius D hσ
  obtain ⟨τ,hτ,hτone,hsmall⟩ := exists_numerical_list_radius hκ
    (show 0 < r/4 by positivity) hB hA L
  obtain ⟨ν,hν,_,hco⟩ := exists_numerical_list_radius hσ
    (show 0 < r/4 by positivity) (by norm_num : (0 : ℝ) ≤ 0) hT.le 0
  let η := min ε (min τ ν)
  have hη : 0 < η := lt_min hε (lt_min hτ hν)
  refine ⟨η,M,κ,σ,hη,((min_le_right _ _).trans (min_le_left _ _)).trans hτone,hM,hκ,hσ,?_⟩
  intro K X hX hXjet
  obtain ⟨Φ,hΦ,hODE,herror⟩ := hflow K X hX hXjet
  have hsol := fun i => primitiveFlowFromLieFamily_ode D (centreBuffer K r)
    (centreBuffer K (r/2)) X hX Φ hκ hODE i (hp i) (hcoeff i)
  have hbound : ∀ i y, y ∈ centreBuffer K r → ‖X i y‖ ≤ B := by
    intro i y hy
    simpa only [norm_iteratedFDeriv_zero] using hXjet y hy i 0 (by omega)
  refine ⟨Φ,hΦ,hODE,fun i => primitiveFlowFromLieFamily_contDiffOn D
    (centreBuffer K (r/2)) Φ hκ hΦ i (hcoeff i),hsol,?_⟩
  intro S hlen htimes hnorm x hx t ht
  have htt : |t| < τ := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htn : |t| < ν := ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htone : |t| ≤ 1 := (htt.trans_le hτone).le
  have htimeκ : A*|t| < κ := by nlinarith [(hsmall t htt).1]
  have htime := scaleTimedPrimitiveSchedule_coarse_time_bound p t S hA htone htimes
  have hball : ball x (r/4) ⊆ (centreBuffer K (r/2) : Set (Fin N → ℝ)) := by
    intro z hz
    exact mem_centreBuffer_iff.mpr ⟨x,hx,ball_subset_ball (by linarith) hz⟩
  have hbudget : ‖x-x‖ + (scaleTimedPrimitiveSchedule p t S).length*(B*(A*|t|)) < r/4 := by
    rw [sub_self,norm_zero,zero_add,scaleTimedPrimitiveSchedule_length]
    have he : (S.length : ℝ)*(B*(A*|t|)) ≤ (L : ℝ)*(B*(A*|t|)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)
    exact he.trans_lt (by nlinarith [(hsmall t htt).2])
  have hpath := timedSchedule_inside_ball_of_budget (primitiveFlowFromLieFamily D Φ κ) x
    hB (by positivity : 0 ≤ A*|t|) htimeκ
    (fun i y hy u hu => primitiveFlow_displacement_le hκ _ y (hsol i y (hball hy)).1
      (fun v hv => ⟨((hsol i y (hball hy)).2 v hv).2,((hsol i y (hball hy)).2 v hv).1⟩)
      (hbound i) (abs_lt.mp hu)) (scaleTimedPrimitiveSchedule p t S) x htime hbudget
  have hinside := timedScheduleInside_mono (primitiveFlowFromLieFamily D Φ κ) hball _ x hpath.1
  refine ⟨hinside,?_⟩
  have hc : ∀ b ∈ S, ‖D.basis.equivFun (timedPrimitiveLieInput b)‖ ≤ T :=
    fun b hb => hprimitive b (htimes b hb)
  have hinput : ∀ b ∈ S, dilatedInputCoordinates D (timedPrimitiveLieInput b) t ∈ ball 0 σ := by
    intro b hb
    exact mem_ball_zero_iff.mpr (((norm_dilatedInputCoordinates_le D _ htone).trans
      (mul_le_mul_of_nonneg_left (hc b hb) (abs_nonneg t))).trans_lt (hco t htn).1)
  have he := scaledTimedSchedule_fromLie_eq_retainedList D (centreBuffer K r)
    (centreBuffer K (r/2)) X hX Φ hκ hODE hcoeff S
    (fun b hb => (htime _ (List.mem_map.mpr ⟨b,hb,rfl⟩)).trans_lt htimeκ) hinput x
    (centreBuffer_self_mem (by positivity) hx) hinside
  rw [he]
  exact herror (S.map (timedPrimitiveLieInput (s := s) (p := p))) (by simpa only [List.length_map] using hlen)
    (fun f hf => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hf; exact hc b hb)
    (htarget _ hnorm) x hx t (ht.trans_le (min_le_left _ _))
end RothschildStein.G3

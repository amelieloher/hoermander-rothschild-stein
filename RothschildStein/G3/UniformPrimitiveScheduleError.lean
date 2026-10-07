-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformRetainedListError
public import RothschildStein.G3.PrimitiveRetainedAdmissibility
public import RothschildStein.G3.WeightedPrimitiveTravel
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- A common actual primitive family has the weighted BCH approximation for
all signed schedules of bounded length, with numerical domain and constants. -/
theorem exists_uniform_primitiveSchedule_BCH_error {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) (hp : ∀ i, (p i : ℕ) ≤ s)
    {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (L : ℕ) :
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
          ∀ S : List (Fin a × Bool), S.length ≤ L → ∀ x ∈ K, ∀ t : ℝ, |t| < η →
            G1.FlowScheduleAdmissible (primitiveFlowFromLieFamily D Φ κ)
              (fun i t => t^(p i : ℕ)) (fun _ => (centreBuffer K (r/2) : Set (Fin N → ℝ)))
              (fun _ => κ) t S x ∧
            ‖G1.runSchedule (fun b y => weightedPrimitiveArc p (primitiveFlowFromLieFamily D Φ κ) b (t,y)) S x -
              finiteLieTimeOneMap Φ (dilatedInputCoordinates D
                (retainedLieListProduct (S.map primitiveScheduleLieInput)) t,x)‖ ≤ M*|t| ^(s+1) := by
  obtain ⟨T,hT,hletter,hproduct⟩ := exists_primitiveSchedule_coefficient_budget D L
  obtain ⟨ε,M,σ,hε,hM,hσ,hflow⟩ := exists_uniform_retainedLie_list_BCH_error
    (N := N) D hs hr hB hT.le L
  obtain ⟨κ,hκ,_,hcoeff⟩ := exists_primitive_rescaling_radius D hσ
  obtain ⟨τ,hτ,hτone,hsmall⟩ := exists_numerical_list_radius hκ
    (show 0 < r/4 by positivity) hB (by norm_num : (0 : ℝ) ≤ 1) L
  let η := min ε τ
  have hη : 0 < η := lt_min hε hτ
  refine ⟨η,M,κ,σ,hη,(min_le_right _ _).trans hτone,hM,hκ,hσ,?_⟩
  intro K X hX hXjet
  obtain ⟨Φ,hΦ,hODE,herror⟩ := hflow K X hX hXjet
  have hsol := fun i => primitiveFlowFromLieFamily_ode D (centreBuffer K r)
    (centreBuffer K (r/2)) X hX Φ hκ hODE i (hp i) (hcoeff i)
  have hbound : ∀ i y, y ∈ centreBuffer K r → ‖X i y‖ ≤ B := by
    intro i y hy
    simpa only [norm_iteratedFDeriv_zero] using hXjet y hy i 0 (by omega)
  refine ⟨Φ,hΦ,hODE,fun i => primitiveFlowFromLieFamily_contDiffOn D
    (centreBuffer K (r/2)) Φ hκ hΦ i (hcoeff i),hsol,?_⟩
  intro S hlen x hx t ht
  have htt : |t| < τ := ht.trans_le (min_le_right _ _)
  have htκ : |t| < κ := by simpa only [mul_one] using (hsmall t htt).1
  have htone : |t| ≤ 1 := (htt.trans_le hτone).le
  have hball : ball x (r/4) ⊆ (centreBuffer K (r/2) : Set (Fin N → ℝ)) := by
    intro z hz
    exact mem_centreBuffer_iff.mpr ⟨x,hx,ball_subset_ball (by linarith) hz⟩
  have htravel : ∀ b ∈ S, ∀ z ∈ ball x (r/4), ‖finiteLieTimeOneMap Φ
      (dilatedInputCoordinates D (primitiveScheduleLieInput b) t,z)-z‖ ≤ B*|t| := by
    intro b _ z hz
    have he := weightedPrimitiveArc_fromLie_eq_endpoint D (centreBuffer K r)
      (centreBuffer K (r/2)) X hX Φ hκ htκ htone hODE hcoeff b (hball hz)
    rw [← he]
    exact norm_weightedPrimitiveArc_displacement_le p _ X hκ hB htκ htone b z
      (hsol b.1 z (hball hz)).1 (hsol b.1 z (hball hz)).2 (hbound b.1)
  have hbudget : ‖x-x‖ + S.length*(B*|t|) < r/4 := by
    rw [sub_self,norm_zero,zero_add]
    have he : (S.length : ℝ)*(B*|t|) ≤ (L : ℝ)*(B*|t|) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)
    exact he.trans_lt (by nlinarith [(hsmall t htt).2])
  have had := primitiveSchedule_fromLie_admissible_of_budget D (centreBuffer K r)
    (centreBuffer K (r/2)) X hX Φ hκ htκ htone (by positivity : 0 ≤ B*|t|)
    hODE hcoeff S x x hball htravel hbudget
  refine ⟨had,?_⟩
  have he := primitiveSchedule_fromLie_eq_retainedList D (centreBuffer K r)
    (centreBuffer K (r/2)) X hX Φ hκ htκ htone hODE hcoeff S x had
  have he' : G1.runSchedule (fun b y => weightedPrimitiveArc p
      (primitiveFlowFromLieFamily D Φ κ) b (t,y)) S x =
      runRetainedLiePointList D Φ (S.map primitiveScheduleLieInput) t x := he
  rw [he']
  exact herror (S.map primitiveScheduleLieInput) (by simpa only [List.length_map] using hlen)
    (fun f hf => by obtain ⟨b,_,rfl⟩ := List.mem_map.mp hf; exact hletter b)
    (hproduct S hlen) x hx t (ht.trans_le (min_le_left _ _))
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.GeneratorConnectivity
public import RothschildStein.G1.LocalQuasiFlowCosts
public import RothschildStein.G1.IntegralCurveCosts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.G1
open G3

/-- Every admissible finite actual flow schedule is a finite
original-generator path in its original domain (BB (1.44), p. 34). -/
theorem finiteGeneratorPath_of_flowSchedule {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (U : Fin m → Set (Fin n → ℝ)) (τ : Fin m → ℝ) (hτ : ∀ i, 0 < τ i)
    (Φ : Fin m → ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ i x, x ∈ U i → Φ i (x,0) = x ∧ ∀ v ∈ Ioo (-τ i) (τ i),
      HasDerivAt (fun z => Φ i (x,z)) (X i (Φ i (x,v))) v ∧ Φ i (x,v) ∈ Ω)
    (T : Fin m → ℝ → ℝ) (t : ℝ) (S : List (Fin m × Bool)) (x : Fin n → ℝ)
    (h : FlowScheduleAdmissible Φ T U τ t S x) :
    FiniteGeneratorPath Ω X x (runSchedule (fun b y => flowArc Φ T b (t,y)) S x) := by
  induction S generalizing x with
  | nil => exact Relation.EqvGen.refl x
  | cons b S ih =>
    obtain ⟨hx,ht,_,htail⟩ := h
    let v := if b.2 then T b.1 t else -T b.1 t
    have hv : v ∈ Ioo (-τ b.1) (τ b.1) := by
      dsimp [v]; split_ifs
      · exact ht
      · constructor <;> linarith [ht.1,ht.2]
    obtain ⟨hs,hm,hd⟩ := integralCurve_generatorArc (hX b.1)
      (show (0 : ℝ) ∈ Ioo (-τ b.1) (τ b.1) from ⟨by linarith [hτ b.1],hτ b.1⟩)
      hv (hΦ b.1 x hx).2
    have ha : IsGeneratorArc Ω X x (flowArc Φ T b (t,x)) := by
      refine ⟨b.1,v,(fun u => Φ b.1 (x,v*u)),hs,hm,hd,?_,?_⟩
      · simpa only [mul_zero] using (hΦ b.1 x hx).1
      · simp only [mul_one,flowArc,v]
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ha) (ih _ htail)

/-- Near zero each actual signed bracket endpoint is joined
by finitely many primitive arcs, retaining all intermediate domains. -/
theorem LocalQuasiFlowData.signedMap_eventually_path {a s n : ℕ} {p : Fin a → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    {D : FreeModelData a s p} {z : Fin n → ℝ} (P : LocalQuasiFlowData Ω X D z)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin a)) (hne : I ≠ []) (hI : wordWeight p I ≤ s) :
    ∀ᶠ q : ℝ × (Fin n → ℝ) in 𝓝 (0,z), FiniteGeneratorPath Ω X q.2 (P.signedMap I q) := by
  have hk : 0 < wordWeight p I := (List.length_pos_iff.mpr hne).trans_le (length_le_weight p I)
  let root := fun h : ℝ => |h| ^ (1 / (wordWeight p I : ℝ))
  have hr : Continuous root := continuous_abs.rpow_const (fun _ => Or.inr (by positivity))
  have hr0 : root 0 = 0 := by
    dsimp [root]; rw [abs_zero,Real.zero_rpow (by positivity : (1 / (wordWeight p I : ℝ)) ≠ 0)]
  have hb := (continuous_snd.continuousAt (x := ((0 : ℝ),z))).preimage_mem_nhds (P.open_U.mem_nhds P.center)
  have ht := ((hr.comp continuous_fst).continuousAt (x := ((0 : ℝ),z))).preimage_mem_nhds
    (Iio_mem_nhds (by simpa only [Function.comp_apply,hr0] using P.η_pos))
  filter_upwards [hb,ht] with q hq hqt
  change q.2 ∈ P.U at hq
  change root q.1 < P.η at hqt
  by_cases hz : q.1 = 0
  · have he : q = (0,q.2) := Prod.ext hz rfl
    rw [he,P.signedMap_zero]; exact Relation.EqvGen.refl _
  have hrt : 0 < root q.1 := Real.rpow_pos_of_pos (abs_pos.mpr hz) _
  have had := P.admissible I hne hI q.2 hq (root q.1) ⟨by linarith [P.η_pos],hqt⟩
  have hp := finiteGeneratorPath_of_flowSchedule X hX (fun _ => P.V) (fun _ => P.κ)
    (fun _ => P.κ_pos) (primitiveFlowFromLieFamily D P.Φ P.κ) P.ode_primitive
    (fun i t => t^(p i : ℕ)) (root q.1)
  have he : P.signedMap I q = if 0 ≤ q.1 then
      quasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I (root q.1) q.2
      else inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D P.Φ P.κ) I (root q.1) q.2 := by
    simp only [signedMap,ite_eq_left hq,signedRootEndpoint]; split_ifs <;> abel
  rw [he]; split_ifs
  · exact hp _ _ had.1
  · exact hp _ _ had.2
end RothschildStein.G1

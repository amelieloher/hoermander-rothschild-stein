-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.CoordinateEndpointReachability
public import RothschildStein.G1.ActualLocalControlUpper
public import RothschildStein.G1.LocalStep
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RothschildStein.G1
open G3

/-- The actual bracket chart's inverse gives an open finite-arc
neighborhood inside any prescribed open domain (BB p. 34). -/
theorem exists_local_generator_connectivity_of_bracketStep {m n s : ℕ}
    (hm : 0 < m) (hs : 1 ≤ s) (w : Fin m → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {W : Set (Fin n → ℝ)} (hW : IsOpen W)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) W)
    {z : Fin n → ℝ} (hz : z ∈ W) (hstep : bracketStepOn {z} w X s) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ z ∈ U ∧ U ⊆ W ∧
      ∀ a ∈ U, ∀ b ∈ U, FiniteGeneratorPath W X a b := by
  classical
  let D := G3.freeModelData w hm hw
  obtain ⟨P⟩ := exists_local_quasi_flow_data D hs hw hW X hX z hz
  obtain ⟨B,hB⟩ := G4.exists_short_frame hstep (mem_singleton z)
  let H := fun i : Fin n => P.signedMap (B i).val
  let F := coordinateEndpointChart H (List.finRange n)
  let A := frameCoordinateEquiv (G4.shortField w X) B z hB
  have hword : ∀ i, (B i).val ≠ [] ∧ wordWeight w (B i).val ≤ s :=
    fun i => (G4.mem_shortWordFamily_iff w _).mp (B i).property
  have hzero : ∀ i x, H i (0,x) = x := fun i x => P.signedMap_zero _ x
  have hreg : ∀ i, ContDiffAt ℝ 1 (H i) (0,z) := fun i =>
    (P.signedMap_regular hW hX hs _ (hword i).1 (hword i).2 P.center).1
  have hder : ∀ i, HasFDerivAt (H i)
      ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) +
        (ContinuousLinearMap.toSpanSingleton ℝ (G4.shortField w X (B i) z)).comp
          (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))) (0,z) := fun i =>
    (P.signedMap_regular hW hX hs _ (hword i).1 (hword i).2 P.center).2
  have hF := coordinateEndpointChart_contDiffAt_zero H hzero (List.finRange n) z hreg
  have hAeq := bracketCoordinateChart_coefficient_derivative (G4.shortField w X) B z hB H hzero hder
  let f := fun u : Fin n → ℝ => F (u,z)
  have hf : ContDiffAt ℝ 1 f 0 := hF.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hi : HasFDerivAt (fun u : Fin n → ℝ => (u,z))
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)) 0 := by
    convert (hasFDerivAt_id (𝕜 := ℝ) (0 : Fin n → ℝ)).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) z (0 : Fin n → ℝ)) using 1 <;> rfl
  have hdf : HasFDerivAt f (A : _ →L[ℝ] _) 0 := by
    have hh := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp 0 hi
    convert hh using 1 <;> try rfl
    exact hAeq.symm
  have hstrict := hf.hasStrictFDerivAt' hdf (by norm_num)
  let e := hstrict.toOpenPartialHomeomorph f
  have he : (e : _ → _) = f := hstrict.toOpenPartialHomeomorph_coe
  have h0 : (0 : Fin n → ℝ) ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hf0 : f 0 = z := coordinateEndpointChart_zero H hzero (List.finRange n) z
  have hp := coordinateEndpointChart_eventually_path X H hzero (List.finRange n) z hreg
    (fun i => P.signedMap_eventually_path hX _ (hword i).1 (hword i).2)
  have hpu := (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually hp
  obtain ⟨r,hr,hrp⟩ := Metric.mem_nhds_iff.mp hpu
  let U := e '' (e.source ∩ ball 0 r) ∩ W
  refine ⟨U,(e.isOpen_image_source_inter isOpen_ball).inter hW,?_,inter_subset_right,?_⟩
  · exact ⟨⟨0,⟨h0,mem_ball_self hr⟩,by rw [he]; exact hf0⟩,hz⟩
  · intro a ha b hb
    obtain ⟨ua,hua,hea⟩ := ha.1
    obtain ⟨ub,hub,heb⟩ := hb.1
    have hpa : FiniteGeneratorPath W X z a := by
      have hh : FiniteGeneratorPath W X z (f ua) := hrp hua.2
      rwa [← he,hea] at hh
    have hpb : FiniteGeneratorPath W X z b := by
      have hh : FiniteGeneratorPath W X z (f ub) := hrp hub.2
      rwa [← he,heb] at hh
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpa) hpb

/-- Pointwise Lie rank gives finite original-generator arcs
inside every prescribed smaller open neighborhood. Drift is included
among the generators; no globally fixed step is needed (BB p. 34). -/
theorem exists_local_generator_connectivity_of_bracketSpansOn {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hrank : bracketSpansOn Ω X)
    (z : Fin n → ℝ) (hz : z ∈ Ω) (W : Set (Fin n → ℝ))
    (hW : IsOpen W) (hzW : z ∈ W) (hWΩ : W ⊆ Ω) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ z ∈ U ∧ U ⊆ W ∧
      ∀ a ∈ U, ∀ b ∈ U, FiniteGeneratorPath W X a b := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    refine ⟨W,hW,hzW,Subset.rfl,?_⟩
    intro a _ b _
    have he : b = a := Subsingleton.elim _ _
    subst b; exact Relation.EqvGen.refl _
  let w : Fin m → ℕ+ := fun _ => 1
  obtain ⟨V,_,hzV,_,_,_,s,hs,hstep⟩ := exists_uniform_step_buffer hΩ
    isCompact_singleton (singleton_subset_iff.mpr hz) w X hX hrank
  have hzstep : bracketStepOn {z} w X s := fun y hy => by
    have he : y = z := mem_singleton_iff.mp hy
    subst y; exact hstep z (subset_closure (hzV (mem_singleton z)))
  have hm : 0 < m := by
    by_contra hh
    have he : m = 0 := Nat.eq_zero_of_not_pos hh
    subst m
    obtain ⟨B,_⟩ := G4.exists_short_frame hzstep (mem_singleton z)
    have hi := ((G4.mem_shortWordFamily_iff w (B ⟨0,hn⟩).val).mp (B ⟨0,hn⟩).property).1
    cases hv : (B ⟨0,hn⟩).val with
    | nil => exact hi hv
    | cons i I => exact Fin.elim0 i
  exact exists_local_generator_connectivity_of_bracketStep hm hs w (fun _ => hs)
    hW X (fun i => (hX i).mono hWΩ) hzW hzstep
end RothschildStein.G1

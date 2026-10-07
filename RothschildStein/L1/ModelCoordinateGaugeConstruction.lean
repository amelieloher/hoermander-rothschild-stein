-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ModelCoordinateData
public import RothschildStein.L1.CanonicalCommonPatchWithRadius
public import RothschildStein.L1.CanonicalAmbientGaugeComparison
public import RothschildStein.L1.CanonicalFrozenDensity
public import RothschildStein.L1.CanonicalVectorApproximation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators ENNReal
namespace RothschildStein.L1
open G3

/-- A free system constructs all the model coordinate clauses and the ambient gauge comparison on a
single source and its complete target family (BB pp. 506–513). -/
theorem exists_modelCoordinateData_with_gauge {k s : ℕ} {w : Fin (k+1) → ℕ+}
    (D : FreeModelData (k+1) s w)
    (V : Opens (Fin (freeDimension (k+1) s w) → ℝ))
    (X : Fin (k+1) → (Fin (freeDimension (k+1) s w) → ℝ) → (Fin (freeDimension (k+1) s w) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) V)
    (x : Fin (freeDimension (k+1) s w) → ℝ) (hx : x ∈ V)
    (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (hstep : bracketStepOn V w X s) (hfree : ∀ y ∈ V, FreeAt w s X y) :
    ∃ A : ModelCoordinateData (V : Set _) X x (modelDataOfFreeModel D),
      ∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ Ω : Set (Fin (freeDimension (k+1) s w) → ℝ),
        (V : Set _) ⊆ Ω → ∀ η ∈ A.U, ∀ ξ ∈ A.U,
        ENNReal.ofReal (rsGauge D.group.weight D.group.weight_pos (A.Θ η ξ)/Cρ) ≤
          controlDistance Ω w X η ξ ∧
        controlDistance Ω w X η ξ ≤ ENNReal.ofReal
          (Cρ*rsGauge D.group.weight D.group.weight_pos (A.Θ η ξ)) := by
  obtain ⟨C,hA⟩ := exists_free_canonical_local_approximation D V X hX x hx (hfree x hx)
  obtain ⟨rρ,Cρ,hrρ,_hrρC,hCρ,hgauge⟩ :=
    exists_canonical_ambient_gauge_comparison D hs hw V.isOpen X hX hstep hfree C
  obtain ⟨U,e,hU,hK,hUV,hxU,hUg,hhalf,hsmall,he,hT,hrad⟩ :=
    C.exists_common_patch_with_radius rρ hrρ
  have hsub : U ⊆ ball x C.radius :=
    hhalf.trans (ball_subset_ball (by linarith [C.radius_pos]))
  have hs : ∀ η ∈ U, ∀ ξ ∈ U, C.theta (η,ξ) ∈ ball 0 C.radius :=
    fun η hη ξ hξ => ball_subset_ball (by linarith [C.radius_pos]) (hsmall η hη ξ hξ)
  have htarget : ∀ η ∈ U, ∀ u ∈ (e η).target, u ∈ ball 0 (C.radius/2) := by
    intro η hη u hu
    rw [(he η hη).2.1] at hu
    obtain ⟨ξ,hξ,rfl⟩ := hu
    exact hsmall η hη ξ hξ
  have hTs : {z | z.1 ∈ U ∧ z.2 ∈ (e z.1).target} ⊆
      ball x C.radius ×ˢ ball 0 C.radius := by
    intro z hz
    exact ⟨hsub hz.1,ball_subset_ball (by linarith [C.radius_pos]) (htarget z.1 hz.1 z.2 hz.2)⟩
  have hY := fun j => G1.wordBracket_contDiffOn V.isOpen X hX (modelBasisWord D j)
  obtain ⟨c,wp,wm,lo,hi,B,hlo,hhi,hB,hc,hcp,hwp,hwm,hzero,hm,hfactor,hcb,hwb⟩ :=
    C.common_density_package V.isOpen hY
  refine ⟨{
    U := U
    isOpen_U := hU
    isCompact_closure_U := hK
    closure_subset_domain := hUV
    center_mem := hxU
    Θ := fun η ξ => C.theta (η,ξ)
    e := e
    R := fun I η u => canonicalWordRemainder D X C I (η,u)
    c := c
    ωp := fun η u => wp (η,u)
    ωm := fun η u => wm (η,u)
    theta_smooth := C.theta_smooth.mono (fun z hz => C.basePatch_subset ⟨hsub hz.1,hsub hz.2⟩)
    chart := ?_
    radial_curve := hrad
    theta_antisymm := fun η hη ξ hξ => C.antisymmetric (η,ξ) (C.basePatch_subset ⟨hsub hη,hsub hξ⟩)
    isOpen_T := hT
    remainder_smooth := fun I => (hA.smooth I).mono hTs
    remainder_weight := fun I _ η hη => hA.frozen_weight η (hsub hη) I
    remainder_origin := fun I _ hI η hη => hA.zero η (hsub hη) I hI
    bracket_approx := fun I _ η hη ξ hξ => canonicalWordRemainder_vector_identity D V X hX C
      (hsub hη) (hsub hξ) (hs η hη ξ hξ) I
    density_smooth := hc.mono hsub
    density_pos := fun η hη => (hcp η (hsub hη)).1
    ωp_smooth := hwp.mono hTs
    ωm_smooth := hwm.mono hTs
    ω_origin := fun η hη => hzero η (hsub hη)
    ωm_eq := fun η _ u => hm (η,u)
    jacobian := fun η hη ξ hξ => C.frozen_density_jacobians c wp wm
      (fun η hη => (hcp η hη).1) hfactor (hsub hη) (hsub hξ) (hs η hη ξ hξ)
    density_bounds := ?_ },Cρ,hCρ,?_⟩
  · intro η hη
    exact ⟨(he η hη).1,fun ξ _ => (he η hη).2.2.1 ξ,
      (he η hη).2.2.2.2.1,(he η hη).2.2.2.2.2,C.theta_diagonal η (hsub hη)⟩
  · intro K _ hKU
    refine ⟨lo,hi,B,C.radius/2,hlo,hhi,hB,half_pos C.radius_pos,?_,?_⟩
    · intro η hη
      exact hcb η (ball_subset_closedBall (hhalf (hKU hη)))
    · intro η hη u hu _
      exact hwb η (ball_subset_closedBall (hhalf (hKU hη))) u
        (ball_subset_closedBall (htarget η (hKU hη) u hu))

  · intro Ω hVΩ η hη ξ hξ
    exact hgauge Ω hVΩ η (hUg hη) ξ (hUg hξ)

end RothschildStein.L1

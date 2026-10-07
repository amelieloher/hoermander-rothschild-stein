-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CertifiedPatch
public import RothschildStein.H3.SobolevRepresentativeTransport
public import RothschildStein.H3.QuasiballCompactClosure
public import RothschildStein.H3.GaugeGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Step 0. Actual bounded-ball particular solutions give local
Sobolev membership and forcing certificates for the original global PDE
solution. Hypoellipticity and uniqueness replace any local regularity input. -/
theorem global_regularity_local_data_of_bounded_ball_solutions {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (u g : (Fin n → ℝ) → ℝ) (hu : MemLp u p (volume : Measure (Fin n → ℝ)))
    (hsolve : ∀ R : ℝ, 0 < R →
      ∃ v : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight H.fields (quasiballDomain G ν 0 R) 2 p v ∧
        ∃ D : WeakDriftOperatorData H.fields (quasiballDomain G ν 0 R) p v,
          D.operator =ᵐ[volume.restrict (quasiballDomain G ν 0 R : Set (Fin n → ℝ))] g)
    (heq : ∀ R : ℝ, 0 < R → ∀ ψ : TestFunction (quasiballDomain G ν 0 R) ℝ (⊤ : ℕ∞),
      Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)
        (TestFunction.monoCLM ℝ
          (Distribution.adjointTest (quasiballDomain G ν 0 R) H.fields (fun _ => 0)
            (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ)) =
        Distribution.ofFun (quasiballDomain G ν 0 R) g volume (⊤ : ℕ∞) ψ) :
    ∀ R : ℝ, 0 < R →
      memSobolevX driftWeight H.fields (quasiballDomain G ν 0 R) 2 p u ∧
      ∃ D : WeakDriftOperatorData H.fields (quasiballDomain G ν 0 R) p u,
        D.operator =ᵐ[volume.restrict (G2.gaugeBall G ν 0 R)] g := by
  intro R hR
  obtain ⟨v, hv, D, hD⟩ := hsolve (2 * R) (by positivity)
  have hcl : closure (quasiballDomain G ν 0 R : Set (Fin n → ℝ)) ⊆
      quasiballDomain G ν 0 (2 * R) := by
    intro x hx
    have hxc := (quasiBall_geometry (G := G) ν.gauge 0 R).2.2.2 hx
    change G2.gaugeDistance G ν x 0 ≤ R at hxc
    change G2.gaugeDistance G ν x 0 < 2 * R
    linarith
  obtain ⟨w, hw, E, hE, hrep⟩ := patch_certified_of_weak_particular_solution
    G H ⊤ (quasiballDomain G ν 0 (2 * R)) (quasiballDomain G ν 0 R)
    le_top (quasiballDomain_closure_compact G ν 0 R) hcl p hp
    (Distribution.ofFun ⊤ u volume (⊤ : ℕ∞)) g v hv D hD (heq (2 * R) (by positivity))
  have huLoc : LocallyIntegrableOn u (⊤ : Opens (Fin n → ℝ)) volume :=
    (hu.locallyIntegrable hp).locallyIntegrableOn _
  have hwLoc := locallyIntegrableOn_of_locallyIntegrable_restrict (hw.1.locallyIntegrable hp)
  have hae := ae_eq_of_ofFun_patch_representation ⊤ (quasiballDomain G ν 0 R)
    le_top u w huLoc hwLoc hrep
  have huS := (S.memSobolevX_congr_ae H.fields (quasiballDomain G ν 0 R)
    driftWeight 2 p hae).mpr hw
  let Eu : WeakDriftOperatorData H.fields (quasiballDomain G ν 0 R) p u := {
    first := E.first
    square := E.square
    first_weak := fun i => S.hasWeakWordDeriv_congr_ae H.fields _ (E.first_weak i) hae.symm ae_eq_rfl
    square_weak := fun i => S.hasWeakWordDeriv_congr_ae H.fields _ (E.square_weak i) hae.symm ae_eq_rfl
    first_memLp := E.first_memLp
    square_memLp := E.square_memLp }
  exact ⟨huS, Eu, hE⟩

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualChartLocalHomeomorph
public import RothschildStein.G4.IntervalChartLift
public import Mathlib.Analysis.Convex.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function Topology unitInterval

namespace RothschildStein.G4

/-- A loop lying in another chart's convex coordinate domain
is null-homotopic there. Actual individual vertical lifts through the target
chart force its small-domain endpoints to agree (BB pp. 456–458). -/
theorem injOn_of_convex_chart_contraction_lifts {n : ℕ}
    {S Q U : Set (Fin n → ℝ)} (hS : Convex ℝ S) (hSQ : S ⊆ Q)
    (hQ : IsOpen Q) (hU : Convex ℝ U)
    (F G Ψ : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F Q)
    (hjac : ∀ u ∈ Q, Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0)
    (hG : ContinuousOn G U) (hΨ : ContinuousOn Ψ (F '' S))
    (hinverse : ∀ u ∈ S, Ψ (F u) ∈ U ∧ G (Ψ (F u)) = F u)
    (hlifts : ∀ z ∈ U, ∀ z' ∈ U, ∀ u ∈ S, F u = G z →
      ∃ θ : ℝ → (Fin n → ℝ), ContinuousOn θ (Icc (0 : ℝ) 1) ∧
        θ 0 = u ∧ MapsTo θ (Icc (0 : ℝ) 1) Q ∧
        EqOn (F ∘ θ) (fun t => G (z + t • (z' - z))) (Icc (0 : ℝ) 1)) :
    InjOn F S := by
  intro u hu v hv huv
  let η : I → (Fin n → ℝ) := fun s => u + s.val • (v - u)
  have hη : Continuous η := continuous_const.add (continuous_subtype_val.smul continuous_const)
  have hηS : ∀ s, η s ∈ S := fun s => hS.add_smul_sub_mem hu hv s.property
  have hFη : Continuous (F ∘ η) :=
    hF.continuousOn.comp_continuous hη (fun s => hSQ (hηS s))
  let z : I → (Fin n → ℝ) := fun s => Ψ (F (η s))
  let z₀ := Ψ (F u)
  have hz : Continuous z := hΨ.comp_continuous hFη (fun s => ⟨η s, hηS s, rfl⟩)
  have hzU : ∀ s, z s ∈ U := fun s => (hinverse _ (hηS s)).1
  have hz₀U : z₀ ∈ U := (hinverse u hu).1
  let K : I × I → (Fin n → ℝ) := fun ts => z ts.2 + ts.1.val • (z₀ - z ts.2)
  have hK : Continuous K := (hz.comp continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_const.sub (hz.comp continuous_snd)))
  have hKU : ∀ ts, K ts ∈ U := fun ts =>
    hU.add_smul_sub_mem (hzU ts.2) hz₀U ts.1.property
  let H : C(I × I, Fin n → ℝ) :=
    ⟨G ∘ K, hG.comp_continuous hK hKU⟩
  let start : C(I, Q) :=
    { toFun := fun s => ⟨η s, hSQ (hηS s)⟩
      continuous_toFun := hη.subtype_mk _ }
  have hvertical : ∀ s : I, ∃ Θ : C(I, Q), Θ 0 = start s ∧
      ∀ t : I, F (Θ t).val = H (t, s) := by
    intro s
    obtain ⟨θ, hcont, hstart, hmap, hproj⟩ := hlifts (z s) (hzU s) z₀ hz₀U
      (η s) (hηS s) (hinverse _ (hηS s)).2.symm
    exact exists_continuousMap_chart_lift F Q
      (fun t => G (z s + t • (z₀ - z s))) θ (start s) hcont hstart hmap hproj
  have hlocal := isLocalHomeomorphOn_of_actual_jacobian hQ F hF hjac
  have hp : IsLocalHomeomorph (fun q : Q => F q.val) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hlocal.comp hQ.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun q _ => q.property))
  have hz0 : z 0 = z₀ := by simp [z, η, z₀]
  have hz1 : z 1 = z₀ := by simp [z, η, z₀, ← huv]
  have hleft : ∀ t, H (t, 0) = F u := by
    intro t
    change G (z 0 + t.val • (z₀ - z 0)) = F u
    rw [hz0, sub_self, smul_zero, add_zero]
    exact (hinverse u hu).2
  have hright : ∀ t, H (t, 1) = F u := by
    intro t
    change G (z 1 + t.val • (z₀ - z 1)) = F u
    rw [hz1, sub_self, smul_zero, add_zero]
    exact (hinverse u hu).2
  have htop : ∀ s, H (1, s) = F u := by
    intro s
    change G (z s + (1 : ℝ) • (z₀ - z s)) = F u
    rw [one_smul, ← add_sub_assoc, add_sub_cancel_left]
    exact (hinverse u hu).2
  have heq := rectangular_initial_endpoints_eq_of_vertical_lifts
    (fun q : Q => F q.val) hp H start hvertical (F u) hleft hright htop
  have hval := congrArg Subtype.val heq
  simpa [start, η] using hval

end RothschildStein.G4

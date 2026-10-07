-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LieBracketAddRight
public import RothschildStein.L1.RadialFrameDifferentiation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Differentiate the actual radial decomposition by an arbitrary field.
Every scalar coefficient derivative is retained explicitly. -/
theorem radial_bracket_differential_identity {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (Ω : Opens E) (A : Fin n → E →L[ℝ] ℝ) (Z : Fin n → E → E)
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (hrad : ∀ u ∈ Ω, ∑ i, A i u • Z i u = u)
    (V : E → E) {u : E} (hu : u ∈ Ω) (d : E) :
    VectorField.lieBracket ℝ V (fun _ => d) u =
      (∑ k, A k d • VectorField.lieBracket ℝ V (Z k) u) +
      (∑ k, A k (V u) • VectorField.lieBracket ℝ (fun _ => d) (Z k) u) +
      ∑ k, A k u • VectorField.lieBracket ℝ V
        (VectorField.lieBracket ℝ (fun _ => d) (Z k)) u := by
  let B := fun k => VectorField.lieBracket ℝ (fun _ => d) (Z k)
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : E => d) Ω := contDiffOn_const
  have hB (k : Fin n) : ContDiffOn ℝ (⊤ : ℕ∞) (B k) Ω := by
    have hh := ((hZ k).fderiv_of_isOpen (m := (⊤ : ℕ∞)) Ω.isOpen (by simp)).clm_apply hc
    apply hh.congr
    intro v _
    simp only [B,VectorField.lieBracket,fderiv_const_apply,zero_apply,sub_zero]
  have hC : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => ∑ k, A k d • Z k v) Ω :=
    ContDiffOn.sum (fun k _ => (hZ k).const_smul _)
  have hS : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => ∑ k, A k v • B k v) Ω :=
    ContDiffOn.sum (fun k _ => (A k).contDiff.contDiffOn.smul (hB k))
  have hdZ (k : Fin n) := ((hZ k).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp)
  have hdB (k : Fin n) := ((hB k).contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp)
  have hg : (fun _ : E => d) =ᶠ[𝓝 u]
      (fun v => (∑ k, A k d • Z k v) + ∑ k, A k v • B k v) :=
    Filter.Eventually.mono (Ω.isOpen.mem_nhds hu) (fun v hv =>
      radial_differential_identity Ω A Z hZ hrad hv d)
  have hV : V =ᶠ[𝓝 u] V := Filter.EventuallyEq.rfl
  rw [hV.lieBracket_vectorField_eq (𝕜 := ℝ) hg,
    lieBracket_fun_add_right V _ _ u
      ((hC.contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))
      ((hS.contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp))]
  have hfirst : VectorField.lieBracket ℝ V (fun v => ∑ k, A k d • Z k v) u =
      ∑ k, A k d • VectorField.lieBracket ℝ V (Z k) u := by
    have hf (k : Fin n) : DifferentiableAt ℝ (fun v => A k d • Z k v) u :=
      (differentiableAt_const (A k d)).fun_smul (hdZ k)
    rw [lieBracket_finset_sum_right Finset.univ V (fun k v => A k d • Z k v) u (fun k _ => hf k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [VectorField.lieBracket_smul_right (differentiableAt_const _) (hdZ k)]
    simp only [fderiv_const_apply,zero_apply,zero_smul,zero_add]
  have hsecond : VectorField.lieBracket ℝ V (fun v => ∑ k, A k v • B k v) u =
      (∑ k, A k (V u) • B k u) + ∑ k, A k u • VectorField.lieBracket ℝ V (B k) u := by
    have hf (k : Fin n) : DifferentiableAt ℝ (fun v => A k v • B k v) u :=
      (A k).differentiableAt.fun_smul (hdB k)
    rw [lieBracket_finset_sum_right Finset.univ V (fun k v => A k v • B k v) u
      (fun k _ => hf k),← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [VectorField.lieBracket_smul_right (A k).differentiableAt (hdB k),
      ContinuousLinearMap.fderiv]
  rw [hfirst,hsecond]
  simp only [B,add_assoc]
end RothschildStein.L1

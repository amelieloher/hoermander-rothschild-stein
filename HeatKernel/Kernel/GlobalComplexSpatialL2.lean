-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalSpatialL2
public import HeatKernel.Semigroup.RealL2Subspace

/-! # Complex spatial L² and the canonical real subspace

Equal measures identify native spatial complex L² with full-volume complex
L². The real-subspace equivalence is isometric, and the resulting embedding
of full-volume real L² preserves the scalar real representative formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Equal measures give a canonical complex L² isometry. -/
def complexL2MeasureEquiv {X : Type*} [MeasurableSpace X] {μ ν : Measure X} (h : μ = ν) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν := by
  subst ν
  exact LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ)

/-- Complex L² transport between equal measures preserves scalar representatives. -/
theorem ae_complexL2MeasureEquiv {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    (h : μ = ν) (f : Lp ℂ 2 μ) : complexL2MeasureEquiv h f =ᵐ[ν] f := by
  subst ν
  exact Filter.EventuallyEq.rfl

/-- Native spatial complex L² is isometric to full-volume complex L². -/
def globalComplexSpatialL2Equiv (n : ℕ) :
    Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (Fin n → ℝ)) :=
  complexL2MeasureEquiv (by simp only [Opens.coe_top, Measure.restrict_univ])

/-- The complex global spatial isometry preserves scalar representatives. -/
theorem ae_globalComplexSpatialL2Equiv {n : ℕ}
    (f : Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))) :
    globalComplexSpatialL2Equiv n f =ᵐ[volume] f := ae_complexL2MeasureEquiv _ f

/-- The canonical real-subspace equivalence is a real linear isometry. -/
def realL2SubspaceIsometry {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] realL2Subspace μ where
  toLinearEquiv := (realL2SubspaceEquiv μ).toLinearEquiv
  norm_map' := norm_realL2SubspaceEquiv μ

/-- Full-volume real L² is isometric to the native complex real subspace. -/
def globalSpatialRealSubspaceEquiv (n : ℕ) :
    Lp ℝ 2 (volume : Measure (Fin n → ℝ)) ≃ₗᵢ[ℝ]
      realL2Subspace (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))) :=
  (globalSpatialL2Equiv n).symm.trans (realL2SubspaceIsometry _)

/-- The native complex real-subspace embedding has the scalar real representative formula. -/
theorem ae_globalSpatialRealSubspaceEquiv {n : ℕ}
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    (globalSpatialRealSubspaceEquiv n f :
      Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))))
        =ᵐ[volume] fun x => (f x : ℂ) := by
  have h := coeFn_l2OfReal
    (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))
    ((globalSpatialL2Equiv n).symm f)
  have hnative : (globalSpatialRealSubspaceEquiv n f :
      Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))))
        =ᵐ[volume] fun x => (((globalSpatialL2Equiv n).symm f x : ℝ) : ℂ) := by
    change l2OfReal (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))
      ((globalSpatialL2Equiv n).symm f) =ᵐ[volume] _
    simpa only [Opens.coe_top, Measure.restrict_univ] using h
  filter_upwards [hnative, ae_globalSpatialL2Equiv_symm f] with x hx hfx
  rw [hx, hfx]

/-- The full-volume complex image of the real-subspace embedding has the same scalar formula. -/
theorem ae_globalComplexSpatialRealEmbedding {n : ℕ}
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    globalComplexSpatialL2Equiv n (globalSpatialRealSubspaceEquiv n f)
      =ᵐ[volume] fun x => (f x : ℂ) :=
  (ae_globalComplexSpatialL2Equiv _).trans (ae_globalSpatialRealSubspaceEquiv f)

end HeatKernel

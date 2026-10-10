-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalComplexSpatialL2
public import HeatKernel.Kernel.ComplexTranslationPullback
public import HeatKernel.Kernel.ComplexDilationUnitary
public import HeatKernel.Kernel.ComplexL2RealDecomposition

/-! # Native complex spatial actions and the real embedding

The global complex spatial isometry transports translation and normalized
dilation to native complex L². Their compatibility with the real embedding
and its real/imaginary spanning follow from the scalar representative formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein TopologicalSpace

namespace HeatKernel

/-- Complex unitary left translation on native spatial L². -/
def nativeComplexLeftTranslationL2 {n : ℕ} (G : HomogeneousGroup n) (a : Fin n → ℝ) :
    Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))) :=
  ((globalComplexSpatialL2Equiv n).trans (complexLeftTranslationL2 G a)).trans
    (globalComplexSpatialL2Equiv n).symm

/-- Native complex left translation intertwines the canonical real embedding. -/
theorem nativeComplexLeftTranslationL2_real_embedding {n : ℕ}
    (G : HomogeneousGroup n) (a : Fin n → ℝ)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    nativeComplexLeftTranslationL2 G a (globalSpatialRealSubspaceEquiv n f) =
      globalSpatialRealSubspaceEquiv n (leftTranslationL2 G a f) := by
  apply (globalComplexSpatialL2Equiv n).injective
  change globalComplexSpatialL2Equiv n ((globalComplexSpatialL2Equiv n).symm
      (complexLeftTranslationL2 G a
        (globalComplexSpatialL2Equiv n (globalSpatialRealSubspaceEquiv n f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact complexLeftTranslationL2_apply_real_embedding G a
    (fun f => globalComplexSpatialL2Equiv n (globalSpatialRealSubspaceEquiv n f))
    ae_globalComplexSpatialRealEmbedding f

/-- Complex unitary normalized dilation on native spatial L². -/
def nativeComplexDilationL2 {n : ℕ} (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r) :
    Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))) :=
  ((globalComplexSpatialL2Equiv n).trans (complexDilationL2Equiv G hr)).trans
    (globalComplexSpatialL2Equiv n).symm

/-- Native complex normalized dilation intertwines the canonical real embedding. -/
theorem nativeComplexDilationL2_real_embedding {n : ℕ}
    (G : HomogeneousGroup n) {r : ℝ} (hr : 0 < r)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    nativeComplexDilationL2 G hr (globalSpatialRealSubspaceEquiv n f) =
      globalSpatialRealSubspaceEquiv n (dilationL2Equiv G hr f) := by
  apply (globalComplexSpatialL2Equiv n).injective
  change globalComplexSpatialL2Equiv n ((globalComplexSpatialL2Equiv n).symm
      (complexDilationL2Equiv G hr
        (globalComplexSpatialL2Equiv n (globalSpatialRealSubspaceEquiv n f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact complexDilationL2Equiv_apply_real_embedding G hr
    (fun f => globalComplexSpatialL2Equiv n (globalSpatialRealSubspaceEquiv n f))
    ae_globalComplexSpatialRealEmbedding f

/-- The canonical real embedding spans native complex spatial L² by real and imaginary parts. -/
theorem exists_nativeComplexSpatial_real_imaginary_decomposition {n : ℕ}
    (z : Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))) :
    ∃ a b : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
      z = (globalSpatialRealSubspaceEquiv n a :
        Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))) +
        Complex.I • (globalSpatialRealSubspaceEquiv n b :
          Lp ℂ 2 (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)))) := by
  obtain ⟨a, b, hz⟩ := exists_real_imaginary_L2_decomposition volume
    (fun f => globalComplexSpatialL2Equiv n (globalSpatialRealSubspaceEquiv n f))
    ae_globalComplexSpatialRealEmbedding (globalComplexSpatialL2Equiv n z)
  refine ⟨a, b, (globalComplexSpatialL2Equiv n).injective ?_⟩
  rw [map_add, map_smul]
  exact hz

end HeatKernel

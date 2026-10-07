-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Locality
public import RothschildStein.S.TestOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n q : ℕ}

/-- Local smooth vector fields extend globally with identical germs
on a prescribed interior compact set (BB p. 68; quantitative). -/
theorem exists_global_field_germ_extension (Ω : Opens (Fin n → ℝ))
    (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ Ω)
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ))) :
    ∃ B : (Fin n → ℝ) → (Fin n → ℝ), ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ x ∈ (K : Set (Fin n → ℝ)), B =ᶠ[𝓝 x] V := by
  obtain ⟨χ,U,hU,hKU,_,hone⟩ := exists_test_plateau Ω K hK
  let B := fun x j => testMultiplierOn Ω (fun y => V y j)
    ((contDiff_apply ℝ ℝ j).comp_contDiffOn hV) χ x
  refine ⟨B,contDiff_pi.mpr (fun j => (testMultiplierOn Ω (fun y => V y j)
    ((contDiff_apply ℝ ℝ j).comp_contDiffOn hV) χ).contDiff),?_⟩
  intro x hx
  filter_upwards [hU.mem_nhds (hKU hx)] with y hy
  funext j
  change χ y * V y j = V y j
  rw [hone hy]
  simp

/-- Field transposes of compact tests depend only on coefficient germs near their support (BB p. 68; quantitative). -/
theorem fieldTranspose_eq_of_coefficient_germs (K : Compacts (Fin n → ℝ))
    (B V : (Fin n → ℝ) → (Fin n → ℝ))
    (hg : ∀ x ∈ (K : Set (Fin n → ℝ)), B =ᶠ[𝓝 x] V)
    (φ : (Fin n → ℝ) → ℝ) (hs : tsupport φ ⊆ K) :
    fieldTranspose B φ = fieldTranspose V φ := by
  funext x
  by_cases hx : x ∈ (K : Set (Fin n → ℝ))
  · have he := ((EventuallyEq.rfl : φ =ᶠ[𝓝 x] φ).smul (hg x hx)).fderiv (𝕜 := ℝ)
    simp only [fieldTranspose,Hormander.Interface.euclideanDivergence,he.eq_of_nhds]
  · have hb : x ∉ tsupport (fieldTranspose B φ) :=
      fun ht => hx (hs (tsupport_fieldTranspose_subset B φ ht))
    have hv : x ∉ tsupport (fieldTranspose V φ) :=
      fun ht => hx (hs (tsupport_fieldTranspose_subset V φ ht))
    rw [image_eq_zero_of_notMem_tsupport hb,image_eq_zero_of_notMem_tsupport hv]

/-- Local scalar coefficients extend smoothly with matching germs
on an interior compact set (BB p. 68; quantitative). -/
theorem exists_global_scalar_germ_extension (Ω : Opens (Fin n → ℝ))
    (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ Ω)
    (a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ))) :
    ∃ b : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧
      ∀ x ∈ (K : Set (Fin n → ℝ)), b =ᶠ[𝓝 x] a := by
  obtain ⟨χ,U,hU,hKU,_,hone⟩ := exists_test_plateau Ω K hK
  refine ⟨testMultiplierOn Ω a ha χ,(testMultiplierOn Ω a ha χ).contDiff,?_⟩
  intro x hx
  filter_upwards [hU.mem_nhds (hKU hx)] with y hy
  change χ y * a y = a y
  rw [hone hy]
  simp

end RothschildStein.S

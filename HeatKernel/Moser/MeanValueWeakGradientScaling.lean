-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSpatialTestTransport
public import RothschildStein.S.WeakDeriv
import Mathlib.Tactic

/-! # Local horizontal weak gradients under spatial group scaling -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A local horizontal weak derivative pulls back with the spatial factor r. Both
local integrability and the literal distributional test identity are transported. -/
theorem hasWeakWordDeriv_spatial_pullback {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    (U V : Opens (Fin N → ℝ))
    (hdom : ∀ x ∈ (V : Set (Fin N → ℝ)), G.mul x₀ (G.dilate r x) ∈ (U : Set _))
    {f g : (Fin N → ℝ) → ℝ} (i : Fin q)
    (h : hasWeakWordDeriv (G.horizontalFields hq) U [i] f g) :
    hasWeakWordDeriv (G.horizontalFields hq) V [i]
      (fun x => f (spatialGroupHomeomorph G x₀ r hr x))
      (fun x => r * g (spatialGroupHomeomorph G x₀ r hr x)) := by
  let B := spatialGroupHomeomorph G x₀ r hr
  let J := ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹)
  have hm : Measure.map B volume = J • volume :=
    map_leftTranslation_dilation_volume G x₀ r hr
  have hloc : ∀ v : (Fin N → ℝ) → ℝ,
      LocallyIntegrableOn v (U : Set (Fin N → ℝ)) volume → ∀ c : ℝ,
      LocallyIntegrableOn (fun x => c * v (B x)) (V : Set (Fin N → ℝ)) volume := by
    intro v hv c
    apply (locallyIntegrableOn_iff V.isOpen.isLocallyClosed).mpr
    intro K hKV hK
    have hKU : B '' K ⊆ (U : Set (Fin N → ℝ)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hdom x (hKV hx)
    have hvK := hv.integrableOn_compact_subset hKU (hK.image B.continuous)
    have hp : MemLp v 1 (volume.restrict (B '' K)) := memLp_one_iff_integrable.mpr hvK
    have hcomp := memLp_comp_restrict_of_scaled_measure B volume hm
      ENNReal.ofReal_ne_top hp
    rw [B.injective.preimage_image] at hcomp
    exact (memLp_one_iff_integrable.mp hcomp).const_mul c
  refine ⟨?_, hloc g h.2.1 r, ?_⟩
  · simpa only [one_mul] using hloc f h.1 1
  · intro φ
    let ηf := (φ : (Fin N → ℝ) → ℝ) ∘ B.symm
    have hη : ContDiff ℝ (⊤ : ℕ∞) ηf :=
      φ.contDiff.comp (contDiff_spatialGroupHomeomorph_symm G x₀ r hr)
    have hηs : tsupport ηf ⊆ (U : Set (Fin N → ℝ)) := by
      intro x hx
      have hx' : B.symm x ∈ tsupport (φ : (Fin N → ℝ) → ℝ) := by
        change x ∈ tsupport ((φ : (Fin N → ℝ) → ℝ) ∘ B.symm) at hx
        rw [tsupport_comp_eq_preimage] at hx
        exact hx
      have hmem : B (B.symm x) ∈ (U : Set (Fin N → ℝ)) :=
        hdom (B.symm x) (φ.tsupport_subset hx')
      simpa only [B.apply_symm_apply] using hmem
    let η : TestFunction U ℝ (⊤ : ℕ∞) :=
      ⟨ηf, hη, φ.hasCompactSupport.comp_homeomorph B.symm, hηs⟩
    have he := h.2.2 η
    have hgz : ∀ x ∉ (U : Set (Fin N → ℝ)), g x * η x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (η.tsupport_subset ht)), mul_zero]
    have hfz : ∀ x ∉ (U : Set (Fin N → ℝ)),
        f x * wordTranspose (G.horizontalFields hq) [i] η x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx
        (η.tsupport_subset (S.tsupport_wordTranspose_subset (G.horizontalFields hq) [i] η ht))),
        mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgz,
      setIntegral_eq_integral_of_forall_compl_eq_zero hfz] at he
    have hi : ∀ v : (Fin N → ℝ) → ℝ, (∫ x, v (B x)) = J.toReal * ∫ x, v x := by
      intro v
      rw [← B.measurableEmbedding.integral_map v, hm, integral_smul_measure]
      rfl
    have ht : ∀ x, wordTranspose (G.horizontalFields hq) [i] η (B x) =
        r⁻¹ * wordTranspose (G.horizontalFields hq) [i] φ x :=
      wordTranspose_spatial_transport_at_image G hq hw x₀ r hr φ.contDiff i
    have he' : (∫ x, g (B x) * φ x) =
        r⁻¹ * ∫ x, f (B x) * wordTranspose (G.horizontalFields hq) [i] φ x := by
      calc
        _ = ∫ x, (fun y => g y * η y) (B x) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => by simp [η, ηf])
        _ = J.toReal * ∫ y, g y * η y := hi (fun y => g y * η y)
        _ = J.toReal * ∫ y, f y * wordTranspose (G.horizontalFields hq) [i] η y := by rw [he]
        _ = ∫ x, f (B x) * wordTranspose (G.horizontalFields hq) [i] η (B x) :=
          (hi (fun y => f y * wordTranspose (G.horizontalFields hq) [i] η y)).symm
        _ = _ := by
          simp_rw [ht]
          rw [show (fun x => f (B x) * (r⁻¹ * wordTranspose (G.horizontalFields hq) [i] φ x)) =
            (fun x => r⁻¹ * (f (B x) * wordTranspose (G.horizontalFields hq) [i] φ x)) by
              funext x; ring, integral_const_mul]
    have hgzV : ∀ x ∉ (V : Set (Fin N → ℝ)), (r * g (B x)) * φ x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.tsupport_subset ht)), mul_zero]
    have hfzV : ∀ x ∉ (V : Set (Fin N → ℝ)),
        f (B x) * wordTranspose (G.horizontalFields hq) [i] φ x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx
        (φ.tsupport_subset (S.tsupport_wordTranspose_subset (G.horizontalFields hq) [i] φ ht))),
        mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgzV,
      setIntegral_eq_integral_of_forall_compl_eq_zero hfzV]
    calc
      _ = r * ∫ x, g (B x) * φ x := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by ring)
      _ = r * (r⁻¹ * ∫ x, f (B x) * wordTranspose (G.horizontalFields hq) [i] φ x) := by rw [he']
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.joinPoint
public import RothschildStein.Definitions.basePoint
public import RothschildStein.Definitions.fiberVolume

/-!
# Tonelli through the coordinate split

The measure-preserving split `ℝⁿ × ℝᵐ ≃ ℝⁿ⁺ᵐ` given by `joinPoint`/`basePoint`, the
quasi-measure-preservation of `basePoint`, and the fiber Tonelli identity
`∫_A F(π ξ) dξ = ∫ F(x) · fiberVolume A x dx` (BB pp. 584–585, Thms 11.40–11.41).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RothschildStein.P2
variable {n m : ℕ}

/-- The tail (vertical) coordinates of a lifted point. -/
def tailPoint (ξ : Fin (n + m) → ℝ) : Fin m → ℝ := fun l => ξ (Fin.natAdd n l)

/-- The measurable equivalence `ℝⁿ × ℝᵐ ≃ᵐ ℝⁿ⁺ᵐ`, `(x, t) ↦ joinPoint x t`. -/
def joinEquiv (n m : ℕ) : ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n + m) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + m) => ℝ) finSumFinEquiv)

theorem joinEquiv_apply (x : Fin n → ℝ) (t : Fin m → ℝ) :
    joinEquiv n m (x, t) = joinPoint x t := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · have h : (Fin.castAdd m j) = finSumFinEquiv (Sum.inl j) :=
      (finSumFinEquiv_apply_left j).symm
    simp only [joinEquiv, joinPoint, Fin.addCases_left, MeasurableEquiv.trans_apply]
    rw [h, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  · have h : (Fin.natAdd n l) = finSumFinEquiv (Sum.inr l) :=
      (finSumFinEquiv_apply_right l).symm
    simp only [joinEquiv, joinPoint, Fin.addCases_right, MeasurableEquiv.trans_apply]
    rw [h, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl

/-- The coordinate split preserves Lebesgue measure. -/
theorem measurePreserving_joinEquiv :
    MeasurePreserving (joinEquiv n m) volume volume := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin m => ℝ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin (n + m) => ℝ) finSumFinEquiv
  exact h2.comp h1

theorem basePoint_joinPoint (x : Fin n → ℝ) (t : Fin m → ℝ) :
    basePoint (joinPoint x t) = x := by
  funext j
  simp [basePoint, joinPoint]

theorem tailPoint_joinPoint (x : Fin n → ℝ) (t : Fin m → ℝ) :
    tailPoint (joinPoint x t) = t := by
  funext l
  simp [tailPoint, joinPoint]

theorem joinPoint_basePoint_tailPoint (ξ : Fin (n + m) → ℝ) :
    joinPoint (basePoint ξ) (tailPoint ξ) = ξ := by
  funext i
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
  · simp [basePoint, joinPoint]
  · simp [tailPoint, joinPoint]

theorem joinEquiv_symm_apply (ξ : Fin (n + m) → ℝ) :
    (joinEquiv n m).symm ξ = (basePoint ξ, tailPoint ξ) := by
  rw [MeasurableEquiv.symm_apply_eq, joinEquiv_apply, joinPoint_basePoint_tailPoint]

theorem continuous_basePoint : Continuous (basePoint : (Fin (n + m) → ℝ) → Fin n → ℝ) :=
  continuous_pi fun _ => continuous_apply _

theorem measurable_basePoint : Measurable (basePoint : (Fin (n + m) → ℝ) → Fin n → ℝ) :=
  continuous_basePoint.measurable

theorem continuous_joinPoint : Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
    joinPoint p.1 p.2) := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · simp only [joinPoint, Fin.addCases_left]
    exact (continuous_apply j).comp continuous_fst
  · simp only [joinPoint, Fin.addCases_right]
    exact (continuous_apply l).comp continuous_snd

theorem measurable_joinPoint : Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
    joinPoint p.1 p.2) :=
  continuous_joinPoint.measurable

/-- `basePoint` is quasi-measure-preserving: preimages of null sets are null. -/
theorem quasiMeasurePreserving_basePoint :
    Measure.QuasiMeasurePreserving (basePoint : (Fin (n + m) → ℝ) → Fin n → ℝ) volume volume := by
  have hfun : (basePoint : (Fin (n + m) → ℝ) → Fin n → ℝ) =
      Prod.fst ∘ (joinEquiv n m).symm := by
    funext ξ
    simp [joinEquiv_symm_apply]
  rw [hfun]
  have h1 : Measure.QuasiMeasurePreserving (joinEquiv n m).symm volume volume :=
    (measurePreserving_joinEquiv.symm (joinEquiv n m)).quasiMeasurePreserving
  have h2 : Measure.QuasiMeasurePreserving (Prod.fst : (Fin n → ℝ) × (Fin m → ℝ) → Fin n → ℝ)
      volume volume := Measure.quasiMeasurePreserving_fst
  exact h2.comp h1

theorem ae_comp_basePoint {P : (Fin n → ℝ) → Prop}
    (h : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), P x) :
    ∀ᵐ ξ ∂(volume : Measure (Fin (n + m) → ℝ)), P (basePoint ξ) :=
  quasiMeasurePreserving_basePoint.ae h

/-- The fiber of `A` over `x` is measurable when `A` is. -/
theorem measurableSet_fiber {A : Set (Fin (n + m) → ℝ)} (hA : MeasurableSet A)
    (x : Fin n → ℝ) : MeasurableSet {t : Fin m → ℝ | joinPoint x t ∈ A} :=
  (measurable_joinPoint.comp (measurable_const.prodMk measurable_id)) hA

/-- Tonelli over the fibers of `π = basePoint`:
`∫_A F (π ξ) dξ = ∫ F x · fiberVolume A x dx`. -/
theorem lintegral_comp_basePoint {A : Set (Fin (n + m) → ℝ)} (hA : MeasurableSet A)
    {F : (Fin n → ℝ) → ℝ≥0∞} (hF : AEMeasurable F volume) :
    ∫⁻ ξ in A, F (basePoint ξ) = ∫⁻ x, F x * fiberVolume A x := by
  obtain ⟨F', hF', hFF'⟩ := hF
  have hae : ∀ᵐ ξ ∂(volume : Measure (Fin (n + m) → ℝ)), F (basePoint ξ) = F' (basePoint ξ) :=
    ae_comp_basePoint hFF'
  rw [lintegral_congr_ae (ae_restrict_of_ae hae)]
  have hR : ∫⁻ x, F x * fiberVolume A x = ∫⁻ x, F' x * fiberVolume A x :=
    lintegral_congr_ae (by filter_upwards [hFF'] with x hx; rw [hx])
  rw [hR]
  rw [← lintegral_indicator hA]
  have hm : Measurable (A.indicator (fun ξ => F' (basePoint ξ))) :=
    (hF'.comp measurable_basePoint).indicator hA
  rw [← (measurePreserving_joinEquiv (n := n) (m := m)).lintegral_comp_emb
    (joinEquiv n m).measurableEmbedding]
  rw [Measure.volume_eq_prod, lintegral_prod
    (fun p => A.indicator (fun ξ => F' (basePoint ξ)) (joinEquiv n m p))
    (hm.comp (joinEquiv n m).measurable).aemeasurable]
  apply lintegral_congr
  intro x
  have h1 : ∀ t : Fin m → ℝ, A.indicator (fun ξ => F' (basePoint ξ)) (joinEquiv n m (x, t)) =
      F' x * {t : Fin m → ℝ | joinPoint x t ∈ A}.indicator 1 t := by
    intro t
    rw [joinEquiv_apply]
    by_cases ht : joinPoint x t ∈ A
    · simp [ht, basePoint_joinPoint]
    · simp [ht]
  simp_rw [h1]
  rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_fiber hA x)),
    lintegral_indicator_one (measurableSet_fiber hA x)]
  rfl

/-- A function a.e. strongly measurable on `V` composes with `π` to an a.e. strongly measurable
function on any lifted set `A` projecting into `V`. -/
theorem aestronglyMeasurable_comp_basePoint {A : Set (Fin (n + m) → ℝ)} {V : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hV : MeasurableSet V) (hproj : ∀ ξ ∈ A, basePoint ξ ∈ V) {f : (Fin n → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict V)) :
    AEStronglyMeasurable (fun ξ => f (basePoint ξ)) (volume.restrict A) := by
  obtain ⟨f', hf'm, hff'⟩ := hf
  have h1 : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), x ∈ V → f x = f' x :=
    (ae_restrict_iff' hV).1 hff'
  have h2 := ae_comp_basePoint (m := m) h1
  refine ⟨fun ξ => f' (basePoint ξ), hf'm.comp_measurable measurable_basePoint, ?_⟩
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hA] with ξ h hξ using h (hproj ξ hξ)

end RothschildStein.P2

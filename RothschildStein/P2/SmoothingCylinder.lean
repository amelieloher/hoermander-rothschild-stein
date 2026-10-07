-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.Smoothing

/-!
# Distributional smoothing, descent: product cylinders, tensor tests and the vertical average

The cylinder `A × B ⊆ ℝⁿ⁺ᵐ` (`A ⊆ ℝⁿ`, `B ⊆ ℝᵐ` open), tensor tests `(φ ⊗ η)(x, t) = φ(x) η(t)`
and the vertical average `ū(x) = ∫ w(x, t) η(t) dt` of a locally integrable `w` (BB p. 609, descent step of the distributional smoothing theorem). The pairing of a tensor test with `w` is computed by Fubini through the
measure-preserving coordinate split `joinEquiv` (`MeasureTheory.integral_prod`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions
namespace RothschildStein.P2
variable {n m : ℕ}

theorem contDiff_tailPoint :
    ContDiff ℝ (⊤ : ℕ∞) (tailPoint : (Fin (n + m) → ℝ) → Fin m → ℝ) :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _

/-- The Euclidean product cylinder `A × B ⊆ ℝⁿ⁺ᵐ`, `{ξ | π ξ ∈ A ∧ τ ξ ∈ B}` (BB p. 610). -/
def cylinder (A : Opens (Fin n → ℝ)) (B : Opens (Fin m → ℝ)) : Opens (Fin (n + m) → ℝ) :=
  ⟨{ξ | basePoint ξ ∈ (A : Set (Fin n → ℝ)) ∧ tailPoint ξ ∈ (B : Set (Fin m → ℝ))},
    (continuous_basePoint.isOpen_preimage _ A.isOpen).inter
      (continuous_tailPoint.isOpen_preimage _ B.isOpen)⟩

section Cylinder

variable {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}

theorem mem_cylinder {ξ : Fin (n + m) → ℝ} :
    ξ ∈ (cylinder A B : Set (Fin (n + m) → ℝ)) ↔
      basePoint ξ ∈ (A : Set (Fin n → ℝ)) ∧ tailPoint ξ ∈ (B : Set (Fin m → ℝ)) := Iff.rfl

theorem joinPoint_mem_cylinder {x : Fin n → ℝ} {t : Fin m → ℝ} :
    joinPoint x t ∈ (cylinder A B : Set (Fin (n + m) → ℝ)) ↔
      x ∈ (A : Set (Fin n → ℝ)) ∧ t ∈ (B : Set (Fin m → ℝ)) := by
  rw [mem_cylinder, basePoint_joinPoint, tailPoint_joinPoint]

/-- The fiber of the cylinder over `z ∈ A` is `B`. -/
theorem fiberVolume_cylinder_of_mem {z : Fin n → ℝ} (hz : z ∈ (A : Set (Fin n → ℝ))) :
    fiberVolume (cylinder A B : Set (Fin (n + m) → ℝ)) z = volume (B : Set (Fin m → ℝ)) := by
  unfold fiberVolume
  congr 1
  ext t
  simp only [mem_ofPred_eq, joinPoint_mem_cylinder, hz, true_and]

/-- The fiber of the cylinder over `z ∉ A` is empty. -/
theorem fiberVolume_cylinder_of_notMem {z : Fin n → ℝ} (hz : z ∉ (A : Set (Fin n → ℝ))) :
    fiberVolume (cylinder A B : Set (Fin (n + m) → ℝ)) z = 0 := by
  unfold fiberVolume
  have : {t : Fin m → ℝ | joinPoint z t ∈ (cylinder A B : Set (Fin (n + m) → ℝ))} = ∅ := by
    ext t
    simp only [mem_ofPred_eq, joinPoint_mem_cylinder, hz, false_and, mem_empty_iff_false]
  rw [this, measure_empty]

/-- The tensor test function `(φ ⊗ η)(x, t) = φ(x) η(t)` on the cylinder. -/
def tensorTest (φ : TestFunction A ℝ (⊤ : ℕ∞)) (η : TestFunction B ℝ (⊤ : ℕ∞)) :
    TestFunction (cylinder A B) ℝ (⊤ : ℕ∞) := by
  have hK : IsCompact ((fun p : (Fin n → ℝ) × (Fin m → ℝ) => joinPoint p.1 p.2) ''
      (tsupport (φ : (Fin n → ℝ) → ℝ) ×ˢ tsupport (η : (Fin m → ℝ) → ℝ))) :=
    (φ.hasCompactSupport.prod η.hasCompactSupport).image continuous_joinPoint
  have hsupp : Function.support (fun ξ : Fin (n + m) → ℝ => φ (basePoint ξ) * η (tailPoint ξ)) ⊆
      (fun p : (Fin n → ℝ) × (Fin m → ℝ) => joinPoint p.1 p.2) ''
        (tsupport (φ : (Fin n → ℝ) → ℝ) ×ˢ tsupport (η : (Fin m → ℝ) → ℝ)) := by
    intro ξ hξ
    have h1 : φ (basePoint ξ) ≠ 0 := left_ne_zero_of_mul hξ
    have h2 : η (tailPoint ξ) ≠ 0 := right_ne_zero_of_mul hξ
    exact ⟨(basePoint ξ, tailPoint ξ), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩,
      joinPoint_basePoint_tailPoint ξ⟩
  refine ⟨fun ξ => φ (basePoint ξ) * η (tailPoint ξ), ?_, ?_, ?_⟩
  · exact (φ.contDiff.comp contDiff_basePoint).mul (η.contDiff.comp contDiff_tailPoint)
  · exact HasCompactSupport.intro hK fun ξ hξ => by
      by_contra h
      exact hξ (hsupp h)
  · refine (closure_minimal hsupp hK.isClosed).trans ?_
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact ⟨by simpa [basePoint_joinPoint] using φ.tsupport_subset hx,
      by simpa [tailPoint_joinPoint] using η.tsupport_subset ht⟩

theorem tensorTest_apply (φ : TestFunction A ℝ (⊤ : ℕ∞)) (η : TestFunction B ℝ (⊤ : ℕ∞))
    (ξ : Fin (n + m) → ℝ) : tensorTest φ η ξ = φ (basePoint ξ) * η (tailPoint ξ) := rfl

theorem tensorTest_joinPoint (φ : TestFunction A ℝ (⊤ : ℕ∞)) (η : TestFunction B ℝ (⊤ : ℕ∞))
    (x : Fin n → ℝ) (t : Fin m → ℝ) : tensorTest φ η (joinPoint x t) = φ x * η t := by
  rw [tensorTest_apply, basePoint_joinPoint, tailPoint_joinPoint]

/-- The fiber integral of a tensor test: `J (φ ⊗ η) = (∫ η) φ`. -/
theorem FiberSetting.test_tensorTest (S : FiberSetting (cylinder A B) A)
    (φ : TestFunction A ℝ (⊤ : ℕ∞)) (η : TestFunction B ℝ (⊤ : ℕ∞)) :
    S.test (tensorTest φ η) = (∫ t : Fin m → ℝ, η t) • φ := by
  apply TestFunction.ext
  intro x
  rw [S.test_apply]
  simp_rw [tensorTest_joinPoint]
  rw [integral_const_mul]
  change φ x * _ = _ * φ x
  ring

/-- With `∫ η = 1`, the fiber integral of `φ ⊗ η` is `φ` (the lift of `φ` is `φ ⊗ η`). -/
theorem FiberSetting.test_tensorTest_of_integral_eq_one (S : FiberSetting (cylinder A B) A)
    (φ : TestFunction A ℝ (⊤ : ℕ∞)) {η : TestFunction B ℝ (⊤ : ℕ∞)}
    (hη : ∫ t : Fin m → ℝ, η t = 1) : S.test (tensorTest φ η) = φ := by
  rw [S.test_tensorTest, hη, one_smul]

end Cylinder

/-- Fubini through the coordinate split: `∫ g = ∫ x ∫ t g(x, t)` for integrable `g` on `ℝⁿ⁺ᵐ`. -/
theorem integral_eq_integral_joinPoint {g : (Fin (n + m) → ℝ) → ℝ} (hg : Integrable g volume) :
    ∫ ξ, g ξ = ∫ x : Fin n → ℝ, ∫ t : Fin m → ℝ, g (joinPoint x t) := by
  rw [← (measurePreserving_joinEquiv (n := n) (m := m)).integral_comp' (f := (joinEquiv n m))
    (g := g)]
  have hint' : Integrable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => g (joinEquiv n m p))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (measurePreserving_joinEquiv.integrable_comp_emb
      (joinEquiv n m).measurableEmbedding).2 hg
  rw [Measure.volume_eq_prod, integral_prod _ hint']
  simp_rw [joinEquiv_apply]

/-- The vertical average `ū(x) = ∫ w(x, t) η(t) dt` of `w` against a fixed `η` (BB p. 609). -/
def fiberAvg (w : (Fin (n + m) → ℝ) → ℝ) (η : (Fin m → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ t : Fin m → ℝ, w (joinPoint x t) * η t

section Cylinder

variable {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}

/-- Fubini for a tensor test: `∫ (φ ⊗ η) w = ∫ φ ū`. -/
theorem integral_tensorTest_smul {w : (Fin (n + m) → ℝ) → ℝ}
    (hw : LocallyIntegrableOn w (cylinder A B : Set (Fin (n + m) → ℝ)) volume)
    (φ : TestFunction A ℝ (⊤ : ℕ∞)) (η : TestFunction B ℝ (⊤ : ℕ∞)) :
    ∫ ξ, tensorTest φ η ξ • w ξ = ∫ x : Fin n → ℝ, φ x * fiberAvg w η x := by
  rw [integral_eq_integral_joinPoint ((tensorTest φ η).integrable_smul hw)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only [fiberAvg]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [tensorTest_joinPoint, smul_eq_mul]
  ring

/-- The vertical average of a function locally integrable on the cylinder is locally integrable
on its base (Fubini on `K × supp η`). -/
theorem locallyIntegrableOn_fiberAvg {w : (Fin (n + m) → ℝ) → ℝ}
    (hw : LocallyIntegrableOn w (cylinder A B : Set (Fin (n + m) → ℝ)) volume)
    (η : TestFunction B ℝ (⊤ : ℕ∞)) :
    LocallyIntegrableOn (fiberAvg w η) (A : Set (Fin n → ℝ)) volume := by
  rw [locallyIntegrableOn_iff A.isOpen.isLocallyClosed]
  intro K hKA hK
  set K'' : Set (Fin (n + m) → ℝ) :=
    (fun p : (Fin n → ℝ) × (Fin m → ℝ) => joinPoint p.1 p.2) ''
      (K ×ˢ tsupport (η : (Fin m → ℝ) → ℝ)) with hK''
  have hK''c : IsCompact K'' := (hK.prod η.hasCompactSupport).image continuous_joinPoint
  have hK''sub : K'' ⊆ (cylinder A B : Set (Fin (n + m) → ℝ)) := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact joinPoint_mem_cylinder.2 ⟨hKA hx, η.tsupport_subset ht⟩
  have hwK : IntegrableOn w K'' volume := hw.integrableOn_compact_subset hK''sub hK''c
  have hg : IntegrableOn (fun ξ : Fin (n + m) → ℝ => w ξ * η (tailPoint ξ)) K'' volume :=
    hwK.mul_continuousOn (η.continuous.comp continuous_tailPoint).continuousOn hK''c
  have hgi : Integrable (K''.indicator fun ξ : Fin (n + m) → ℝ => w ξ * η (tailPoint ξ)) volume :=
    (integrable_indicator_iff hK''c.measurableSet).2 hg
  have hprod : Integrable (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
      K''.indicator (fun ξ : Fin (n + m) → ℝ => w ξ * η (tailPoint ξ)) (joinEquiv n m p))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (measurePreserving_joinEquiv.integrable_comp_emb
      (joinEquiv n m).measurableEmbedding).2 hgi
  have hax := hprod.integral_prod_left
  have heq : (fun x : Fin n → ℝ => ∫ t : Fin m → ℝ,
      K''.indicator (fun ξ : Fin (n + m) → ℝ => w ξ * η (tailPoint ξ)) (joinEquiv n m (x, t))) =
      K.indicator (fiberAvg w η) := by
    funext x
    simp_rw [joinEquiv_apply]
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      by_cases ht : t ∈ tsupport (η : (Fin m → ℝ) → ℝ)
      · rw [indicator_of_mem (show joinPoint x t ∈ K'' from ⟨(x, t), ⟨hx, ht⟩, rfl⟩), tailPoint_joinPoint]
      · rw [indicator_of_notMem, image_eq_zero_of_notMem_tsupport ht, mul_zero]
        rintro ⟨⟨x', t'⟩, ⟨_, ht'⟩, hh⟩
        have : t' = t := by
          have := congrArg tailPoint hh
          simpa [tailPoint_joinPoint] using this
        exact ht (this ▸ ht')
    · rw [indicator_of_notMem hx]
      refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans (integral_zero _ _)
      rw [indicator_of_notMem]
      rintro ⟨⟨x', t'⟩, ⟨hx', _⟩, hh⟩
      have : x' = x := by
        have := congrArg basePoint hh
        simpa [basePoint_joinPoint] using this
      exact hx (this ▸ hx')
  rw [heq] at hax
  exact (integrable_indicator_iff hK.measurableSet).1 hax

end Cylinder

end RothschildStein.P2

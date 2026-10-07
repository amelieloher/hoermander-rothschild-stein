-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.NestedDistributionRepresentatives
public import RothschildStein.Definitions.memSobolevXLoc
public import RothschildStein.Definitions.representsDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology

/-- Sobolev representatives on an increasing open exhaustion
give one actual fixed local Sobolev representative of the original
arbitrary distribution. Selection uses the first patch containing each point. -/
theorem exists_local_sobolev_representative_of_exhaustion {n m : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : ℕ → Opens (Fin n → ℝ))
    (hmono : Monotone U) (hU : ∀ j, U j ≤ Ω)
    (hcover : ∀ x ∈ (Ω : Set (Fin n → ℝ)), ∃ j, x ∈ U j)
    (hcofinal : ∀ s : Set (Fin n → ℝ), IsCompact s → s ⊆ Ω → ∃ j, s ⊆ U j)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (v : ℕ → (Fin n → ℝ) → ℝ)
    (hv : ∀ j, memSobolevX w X (U j) k p (v j) ∧
      ∀ ψ : TestFunction (U j) ℝ (⊤ : ℕ∞),
        T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x * v j x) :
    ∃ u : (Fin n → ℝ) → ℝ,
      memSobolevXLoc w X Ω k p u ∧ representsDistribution Ω T u := by
  classical
  let index (x : Fin n → ℝ) : ℕ := if hx : x ∈ (Ω : Set (Fin n → ℝ)) then
    Nat.find (hcover x hx) else 0
  let u : (Fin n → ℝ) → ℝ := fun x => v (index x) x
  have hloc (j : ℕ) : LocallyIntegrableOn (v j) (U j : Set (Fin n → ℝ)) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((hv j).1.1.locallyIntegrable hp)
  have hae (j : ℕ) : u =ᵐ[volume.restrict (U j : Set (Fin n → ℝ))] v j := by
    have hall : ∀ᵐ x ∂volume, ∀ i : ℕ, i ≤ j → x ∈ U i → v i x = v j x := by
      apply ae_all_iff.mpr
      intro i
      by_cases hij : i ≤ j
      · have hh := ae_eq_of_nested_distribution_representatives Ω (U j) (U i)
          (hU j) (hmono hij) T (v i) (v j) (hloc i) (hloc j) (hv i).2 (hv j).2
        have hh' := (ae_restrict_iff' (U i).isOpen.measurableSet).mp hh
        filter_upwards [hh'] with x hx
        exact fun _ => hx
      · exact Eventually.of_forall (fun _ h => (hij h).elim)
    apply (ae_restrict_iff' (U j).isOpen.measurableSet).mpr
    filter_upwards [hall] with x hx hxj
    have hxΩ := hU j hxj
    have hi : Nat.find (hcover x hxΩ) ≤ j := Nat.find_min' _ hxj
    have him : x ∈ U (Nat.find (hcover x hxΩ)) := Nat.find_spec (hcover x hxΩ)
    have hindex : index x = Nat.find (hcover x hxΩ) := by
      simp [index, hxΩ]
    change v (index x) x = v j x
    rw [hindex]
    exact hx _ hi him
  have hSob (j : ℕ) : memSobolevX w X (U j) k p u :=
    (S.memSobolevX_congr_ae X (U j) w k p (hae j)).mpr (hv j).1
  have huLoc : LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume := by
    intro x hx
    obtain ⟨j, hj⟩ := hcover x hx
    have hh := locallyIntegrableOn_of_locallyIntegrable_restrict ((hSob j).1.locallyIntegrable hp)
    have hxint := hh x hj
    rw [(U j).isOpen.nhdsWithin_eq hj] at hxint
    exact hxint.filter_mono nhdsWithin_le_nhds
  refine ⟨u, ?_, huLoc, ?_⟩
  · intro V hVK hVΩ
    obtain ⟨j, hj⟩ := hcofinal (closure (V : Set (Fin n → ℝ))) hVK hVΩ
    exact S.memSobolevX_restrict w X (U j) V (subset_closure.trans hj) (hSob j)
  · ext ψ
    obtain ⟨j, hj⟩ := hcofinal (tsupport ψ) ψ.hasCompactSupport ψ.tsupport_subset
    let ψj : TestFunction (U j) ℝ (⊤ : ℕ∞) :=
      ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hj⟩
    have htest : (TestFunction.monoCLM ℝ ψj : TestFunction Ω ℝ (⊤ : ℕ∞)) = ψ := by
      ext x
      simp [TestFunction.monoCLM_apply, hU j, ψj]
    have hh := (hv j).2 ψj
    rw [htest] at hh
    rw [Distribution.ofFun_apply huLoc]
    simp only [smul_eq_mul]
    refine hh.trans (integral_congr_ae ?_)
    have he := (ae_restrict_iff' (U j).isOpen.measurableSet).mp (hae j).symm
    filter_upwards [he] with x hx
    by_cases hxj : x ∈ U j
    · exact congrArg (fun z => ψj x * z) (hx hxj)
    · have hz : ψj x = 0 := ψj.zero_on_compl hxj
      have hzψ : ψ x = 0 := hz
      simp only [hz, hzψ, zero_mul]

end RothschildStein.H3

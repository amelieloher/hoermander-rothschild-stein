-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SupportedBallCrossing
public import RothschildStein.S.HolderBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n q : ℕ}

/-- Extending a compactly supported function by zero preserves
its Hölder seminorm on any larger subset of the fixed ambient domain.
The curve crossing stays inside the open ball (BB Prop 2.18(iii), p. 85). The compatible distance induces the Euclidean subtype topology and is locally comparable. -/
theorem holderSeminorm_eq_on_supported_ball
    (Ω : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hG : G.d = controlDistance (Ω : Set (Fin n → ℝ)) w X)
    (hw : ∀ i,(w i : ℕ) ≤ 2) (x₀ : Ω) (R : ℝ≥0∞)
    {α : ℝ} (hα : 0 < α) (f : (Fin n → ℝ) → ℝ)
    {K V : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKB : K ⊆ {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R})
    (hBV : {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R} ⊆ V)
    (hVΩ : V ⊆ Ω) (hz : ∀ z ∈ V \ K,f z = 0) :
    holderSeminorm G.d α V f =
      holderSeminorm G.d α {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R} f := by
  let B := {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R}
  apply le_antisymm ?_ (holderSeminorm_mono G.d α V f hBV)
  apply sInf_le_sInf
  rintro C ⟨hC,hbound⟩
  refine ⟨hC,?_⟩
  have hmixed : ∀ x ∈ B,∀ y ∈ V,y ∉ B → G.d x y < ∞ →
      ENNReal.ofReal |f x-f y| ≤ C*(G.d x y)^α := by
    intro x hx y hy hyB hxy
    have hyK : y ∉ K := fun h => hyB (hKB h)
    have hfy := hz y ⟨hy,hyK⟩
    by_cases hxK : x ∈ K
    · have ht : Tendsto (fun ε : ℝ => C*(ENNReal.ofReal ((G.d x y).toReal+ε))^α)
          (𝓝[>] 0) (𝓝 (C*(G.d x y)^α)) := by
        have ha : Tendsto (fun ε : ℝ => (G.d x y).toReal+ε) (𝓝[>] 0)
            (𝓝 ((G.d x y).toReal)) := by
          have hc : ContinuousAt (fun ε : ℝ => (G.d x y).toReal+ε) 0 := by fun_prop
          simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
        have he := ((ENNReal.continuous_ofReal.tendsto _).comp ha).ennrpow_const α
        simpa only [Function.comp_def,ENNReal.ofReal_toReal hxy.ne] using
          (ENNReal.continuous_const_mul hC.ne).tendsto _ |>.comp he
      apply ge_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      have hd : G.d x y < ENNReal.ofReal ((G.d x y).toReal+ε) :=
        (ENNReal.lt_ofReal_iff_toReal_lt hxy.ne).mpr (by linarith)
      obtain ⟨z,hzΩ,hzB,hzK,hxz⟩ := exists_interior_zero_support_crossing Ω G w X hG hw
        x₀ hK (fun z hz => hKB hz) hxK (hVΩ hy) (fun h => hyB ⟨hVΩ hy,h⟩) hd
      have hfz := hz z ⟨hBV ⟨hzΩ,hzB⟩,hzK⟩
      have hi := hbound x hx z ⟨hzΩ,hzB⟩
        (hxz.trans_lt ENNReal.ofReal_lt_top)
      rw [hfz] at hi
      rw [hfy]
      exact hi.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hxz hα.le) C)
    · rw [hz x ⟨hBV hx,hxK⟩,hfy]
      simp only [sub_self,abs_zero,ENNReal.ofReal_zero,zero_le]
  intro x hx y hy hxy
  by_cases hxB : x ∈ B
  · by_cases hyB : y ∈ B
    · exact hbound x hxB y hyB hxy
    · exact hmixed x hxB y hy hyB hxy
  · by_cases hyB : y ∈ B
    · have hs := G.distance_symm ⟨x,hVΩ hx⟩ ⟨y,hVΩ hy⟩
      have hi := hmixed y hyB x hx hxB (by rwa [hs] at hxy)
      simpa only [hs,abs_sub_comm] using hi
    · rw [hz x ⟨hx,fun h => hxB (hKB h)⟩,hz y ⟨hy,fun h => hyB (hKB h)⟩]
      simp only [sub_self,abs_zero,ENNReal.ofReal_zero,zero_le]

end RothschildStein.S

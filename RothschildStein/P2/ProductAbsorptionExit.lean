-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ControlCurveCertificates
public import RothschildStein.S.HolderBounds
public import RothschildStein.G1.ControlledReparam
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Hölder zero extension of cutoff products (first exit)

Part of the zero-extension product estimates (BB p. 85, Prop 2.18(iii), by a first-exit argument). The
zero-extension step of `RothschildStein.S.holderSeminorm_eq_on_supported_ball` is stated for a
control ball. The zero-extension argument applies for an arbitrary Euclidean-open set `U` (the open quasi-ball `U_s^ρ`):
for `K ⊂ U` compact and a function vanishing on `V \ K`, an admissible curve with parameter
`δ > d(x, y)` from `x ∈ K` to `y ∉ U` first exits an intermediate compact neighbourhood `L` of
`K` inside `U` at a point `z ∈ U \ K`; there `f = 0`, and (HD4a) gives `d(x, z) ≤ δ`. The Hölder
seminorm (and the full norm) of `f` on any `V ⊇ U` therefore equals that on `U`, with no
shrinking support-margin constant.

The statements use the weighted control distance of an arbitrary ambient set `Ω` and weights
`≤ 2` (no distance-geometry hypothesis is needed for this step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RothschildStein.P2

variable {n q : ℕ}

/-- First exit. A controlled curve with parameter `δ > d(x, y)`
from `x ∈ K` to `y ∉ U`, `K ⊂ U` compact and `U` open, reaches a point `z ∈ U \ K` of the ambient
set at distance at most `δ` from `x` (BB p. 85, corrected, with an open set in place of the ball). -/
theorem exists_open_support_crossing {Ω : Set (Fin n → ℝ)} {w : Fin q → ℕ+}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} (hw : ∀ i, (w i : ℕ) ≤ 2)
    {K U : Set (Fin n → ℝ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {x y : Fin n → ℝ} (hx : x ∈ K) (hy : y ∉ U) {δ : ℝ}
    (hd : controlDistance Ω w X x y < ENNReal.ofReal δ) :
    ∃ z : Fin n → ℝ, z ∈ Ω ∧ z ∈ U ∧ z ∉ K ∧ controlDistance Ω w X x z ≤ ENNReal.ofReal δ := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨γ, hγ, h0, h1, hcts, hbound⟩ := S.exists_controlled_curve_distance_certificate hw hd
  set T : Set ℝ := Icc (0 : ℝ) 1 ∩ γ ⁻¹' (interior L)ᶜ with hT
  have hTc : IsClosed T := hcts.preimage_isClosed_of_isClosed isClosed_Icc isOpen_interior.isClosed_compl
  have h1T : (1 : ℝ) ∈ T := by
    refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    show γ 1 ∉ interior L
    rw [h1]
    exact fun h => hy (hLU (interior_subset h))
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  have hmem : sInf T ∈ T := hTc.csInf_mem ⟨1, h1T⟩ hTb
  set t := sInf T with ht
  have ht01 : t ∈ Icc (0 : ℝ) 1 := hmem.1
  have hγt : γ t ∉ interior L := hmem.2
  have ht0 : 0 < t := by
    rcases ht01.1.eq_or_lt with h | h
    · exfalso
      apply hγt
      rw [← h, h0]
      exact hKL hx
    · exact h
  have hbefore : ∀ s ∈ Ico (0 : ℝ) t, γ s ∈ interior L := by
    intro s hs
    by_contra hnot
    have hsT : s ∈ T := ⟨⟨hs.1, hs.2.le.trans ht01.2⟩, hnot⟩
    exact absurd (csInf_le hTb hsT) (not_le.2 hs.2)
  have hcl : γ t ∈ closure (γ '' Ico (0 : ℝ) t) := by
    have hsub : Ico (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 :=
      Ico_subset_Icc_self.trans (Icc_subset_Icc_right ht01.2)
    refine ContinuousWithinAt.mem_closure_image ((hcts t ht01).mono hsub) ?_
    rw [closure_Ico ht0.ne]
    exact ⟨ht0.le, le_rfl⟩
  have hzL : γ t ∈ L := by
    have : closure (γ '' Ico (0 : ℝ) t) ⊆ L := by
      refine closure_minimal ?_ hLc.isClosed
      rintro _ ⟨s, hs, rfl⟩
      exact interior_subset (hbefore s hs)
    exact this hcl
  refine ⟨γ t, hγ.2.2.1 ht01, hLU hzL, fun hk => hγt (hKL hk), ?_⟩
  have hb := hbound 0 ⟨le_rfl, zero_le_one⟩ t ht01
  rw [h0] at hb
  have hδ : 0 ≤ δ := hγ.1.le
  have hs : Real.sqrt |0 - t| ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by simpa only [zero_sub, abs_neg, abs_of_nonneg ht01.1, one_pow] using ht01.2⟩
  exact hb.trans (ENNReal.ofReal_le_ofReal (by nlinarith))

/-- The Hölder seminorm of a function vanishing on `V \ K`, for a
compact `K` inside an open `U ⊆ V ⊆ Ω`, is the same on `V` and on `U`
(BB p. 85, Prop 2.18(iii), repaired for an open set; first-exit argument). -/
theorem holderSeminorm_eq_of_compact_support_open {Ω : Set (Fin n → ℝ)} {w : Fin q → ℕ+}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} (hw : ∀ i, (w i : ℕ) ≤ 2) {α : ℝ} (hα : 0 < α)
    (f : (Fin n → ℝ) → ℝ) {K U V : Set (Fin n → ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (hz : ∀ z ∈ V \ K, f z = 0) :
    holderSeminorm (controlDistance Ω w X) α V f =
      holderSeminorm (controlDistance Ω w X) α U f := by
  apply le_antisymm ?_ (S.holderSeminorm_mono _ α V f hUV)
  apply sInf_le_sInf
  rintro C ⟨hC, hbound⟩
  refine ⟨hC, ?_⟩
  have hmixed : ∀ x ∈ U, ∀ y ∈ V, y ∉ U → controlDistance Ω w X x y < ⊤ →
      ENNReal.ofReal |f x - f y| ≤ C * (controlDistance Ω w X x y) ^ α := by
    intro x hx y hy hyU hxy
    have hyK : y ∉ K := fun h => hyU (hKU h)
    have hfy := hz y ⟨hy, hyK⟩
    by_cases hxK : x ∈ K
    · have ht : Tendsto (fun ε : ℝ => C * (ENNReal.ofReal ((controlDistance Ω w X x y).toReal + ε)) ^ α)
          (𝓝[>] 0) (𝓝 (C * (controlDistance Ω w X x y) ^ α)) := by
        have ha : Tendsto (fun ε : ℝ => (controlDistance Ω w X x y).toReal + ε) (𝓝[>] 0)
            (𝓝 ((controlDistance Ω w X x y).toReal)) := by
          have hc : ContinuousAt (fun ε : ℝ => (controlDistance Ω w X x y).toReal + ε) 0 := by
            fun_prop
          simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
        have he := ((ENNReal.continuous_ofReal.tendsto _).comp ha).ennrpow_const α
        simpa only [Function.comp_def, ENNReal.ofReal_toReal hxy.ne] using
          (ENNReal.continuous_const_mul hC.ne).tendsto _ |>.comp he
      apply ge_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      have hd : controlDistance Ω w X x y <
          ENNReal.ofReal ((controlDistance Ω w X x y).toReal + ε) :=
        (ENNReal.lt_ofReal_iff_toReal_lt hxy.ne).mpr (by linarith)
      obtain ⟨z, hzΩ, hzU, hzK, hxz⟩ := exists_open_support_crossing hw hK hU hKU hxK hyU hd
      have hfz := hz z ⟨hUV hzU, hzK⟩
      have hi := hbound x hx z hzU (hxz.trans_lt ENNReal.ofReal_lt_top)
      rw [hfz] at hi
      rw [hfy]
      exact hi.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hxz hα.le) C)
    · rw [hz x ⟨hUV hx, hxK⟩, hfy]
      simp only [sub_self, abs_zero, ENNReal.ofReal_zero, zero_le]
  intro x hx y hy hxy
  by_cases hxU : x ∈ U
  · by_cases hyU : y ∈ U
    · exact hbound x hxU y hyU hxy
    · exact hmixed x hxU y hy hyU hxy
  · by_cases hyU : y ∈ U
    · have hs := G1.controlDistance_symm Ω w X x y
      have hi := hmixed y hyU x hx hxU (by rwa [hs] at hxy)
      simpa only [hs, abs_sub_comm] using hi
    · rw [hz x ⟨hx, fun h => hxU (hKU h)⟩, hz y ⟨hy, fun h => hyU (hKU h)⟩]
      simp only [sub_self, abs_zero, ENNReal.ofReal_zero, zero_le]

/-- The full Hölder norm of a function vanishing on `V \ K`
agrees on `V` and on the open set `U ⊇ K` (zero extension, first exit). -/
theorem holderENorm_eq_of_compact_support_open {Ω : Set (Fin n → ℝ)} {w : Fin q → ℕ+}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} (hw : ∀ i, (w i : ℕ) ≤ 2) {α : ℝ} (hα : 0 < α)
    (f : (Fin n → ℝ) → ℝ) {K U V : Set (Fin n → ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (hz : ∀ z ∈ V \ K, f z = 0) :
    holderENorm (controlDistance Ω w X) α V f =
      holderENorm (controlDistance Ω w X) α U f := by
  have hs : (⨆ z : V, ENNReal.ofReal |f z.val|) = ⨆ z : U, ENNReal.ofReal |f z.val| := by
    apply le_antisymm
    · apply iSup_le
      intro z
      by_cases hzU : z.val ∈ U
      · exact le_iSup_of_le ⟨z.val, hzU⟩ le_rfl
      · rw [hz z.val ⟨z.property, fun h => hzU (hKU h)⟩, abs_zero, ENNReal.ofReal_zero]
        exact zero_le
    · apply iSup_le
      intro z
      exact le_iSup_of_le ⟨z.val, hUV z.property⟩ le_rfl
  unfold holderENorm
  rw [hs, holderSeminorm_eq_of_compact_support_open hw hα f hK hU hKU hUV hz]

/-- Hölder zero extension of a product `v ζ` (`ζ` a cutoff with
`tsupport ζ ⊆ K ⊂ U`): the seminorm and the full norm of the product are the same on `U` and on
any larger `V ⊆ Ω`; no value of `v` outside `U` enters, and no shrinking support margin appears. -/
theorem holderENorm_cutoff_product_eq {Ω : Set (Fin n → ℝ)} {w : Fin q → ℕ+}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} (hw : ∀ i, (w i : ℕ) ≤ 2) {α : ℝ} (hα : 0 < α)
    (v ζ : (Fin n → ℝ) → ℝ) {K U V : Set (Fin n → ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hUV : U ⊆ V) (hζ : ∀ z, z ∉ K → ζ z = 0) :
    holderENorm (controlDistance Ω w X) α V (fun x => v x * ζ x) =
      holderENorm (controlDistance Ω w X) α U (fun x => v x * ζ x) :=
  holderENorm_eq_of_compact_support_open hw hα _ hK hU hKU hUV
    (fun z hz => by simp [hζ z hz.2])

end RothschildStein.P2

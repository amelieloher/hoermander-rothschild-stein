-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SupportedHolderNormExtension
public import RothschildStein.S.HolderListSums
public import RothschildStein.S.HolderProducts

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.S
variable {n q m : ℕ}

/-- Any compact subordinate finite partition gives the
source covering inequality with constant 1 plus the sum of the cutoff
norms; connectedness is unnecessary (BB (2.23), p. 85; (11.79), p. 592). -/
theorem holderENorm_finite_partition_cover_le
    (Ω : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hG : G.d = controlDistance (Ω : Set (Fin n → ℝ)) w X)
    (hw : ∀ i,(w i : ℕ) ≤ 2) (centers : Fin m → Ω) (R : ℝ≥0∞)
    {α : ℝ} (hα : 0 < α) (f : (Fin n → ℝ) → ℝ)
    (ζ : Fin m → (Fin n → ℝ) → ℝ)
    (hcompact : ∀ i,HasCompactSupport (ζ i))
    (hsupport : ∀ i,tsupport (ζ i) ⊆ {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < R})
    (hfn : ∀ i,holderENorm G.d α {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < R} f < ∞)
    (hζn : ∀ i,holderENorm G.d α {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < R} (ζ i) < ∞)
    {U : Set (Fin n → ℝ)}
    (hU : U ⊆ ⋃ i,{z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < R})
    (hpart : ∀ z ∈ U,∑ i,ζ i z = 1) :
    holderENorm G.d α U f ≤
      (1+∑ i,holderENorm G.d α {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < R} (ζ i))*
        ∑ i,holderENorm G.d α {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < R} f := by
  let B := fun i : Fin m => {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < R}
  let V := ⋃ i,B i
  have hVΩ : V ⊆ Ω := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact hi.1
  have hsep : ∀ z ∈ V,∀ y ∈ V,G.d z y = 0 → z = y := by
    intro z hz y hy hzy
    exact congrArg Subtype.val ((G.distance_eq_zero_iff ⟨z,hVΩ hz⟩ ⟨y,hVΩ hy⟩).mp hzy)
  have heq : ∀ i,holderENorm G.d α V (fun z => f z*ζ i z) = holderENorm G.d α (B i) (fun z => f z*ζ i z) := by
    intro i
    apply holderENorm_eq_on_supported_ball Ω G w X hG hw (centers i) R hα _ (hcompact i) (hsupport i)
      (subset_iUnion B i) hVΩ
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz.2,mul_zero]
  have hprod : ∀ i,holderENorm G.d α V (fun z => f z*ζ i z) ≤ holderENorm G.d α (B i) f *holderENorm G.d α (B i) (ζ i) := by
    intro i
    rw [heq i]
    exact holderENorm_mul_le G.d hα (B i)
      (fun z hz y hy hzy => congrArg Subtype.val ((G.distance_eq_zero_iff ⟨z,hz.1⟩ ⟨y,hy.1⟩).mp hzy))
      f (ζ i) (hfn i) (hζn i)
  have hsum := holderENorm_listSum_le G.d α V hα hsep Finset.univ.toList
    (fun i z => f z*ζ i z) (fun i _ => (hprod i).trans_lt (ENNReal.mul_lt_top (hfn i) (hζn i)))
  have hs : holderENorm G.d α V (fun z => ∑ i,f z*ζ i z) ≤
      ∑ i,holderENorm G.d α V (fun z => f z*ζ i z) := by
    simpa only [Finset.sum_map_toList] using hsum
  have he : EqOn (fun z => ∑ i,f z*ζ i z) f U := by
    intro z hz
    dsimp only
    rw [← Finset.mul_sum,hpart z hz,mul_one]
  calc
    holderENorm G.d α U f = holderENorm G.d α U (fun z => ∑ i,f z*ζ i z) :=
      (holderENorm_congr G.d α U _ he).symm
    _ ≤ holderENorm G.d α V (fun z => ∑ i,f z*ζ i z) := holderENorm_mono G.d α V _ hU
    _ ≤ ∑ i,holderENorm G.d α V (fun z => f z*ζ i z) := hs
    _ ≤ ∑ i,holderENorm G.d α (B i) f*holderENorm G.d α (B i) (ζ i) :=
      Finset.sum_le_sum (fun i _ => hprod i)
    _ ≤ ∑ i,(∑ j,holderENorm G.d α (B j) f)*holderENorm G.d α (B i) (ζ i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_left (Finset.single_le_sum (f := fun j : Fin m => holderENorm G.d α (B j) f) (fun j _ => zero_le) (Finset.mem_univ i)) _)
    _ = (∑ i,holderENorm G.d α (B i) (ζ i))*(∑ j,holderENorm G.d α (B j) f) := by
      rw [← Finset.mul_sum,mul_comm]
    _ ≤ (1+∑ i,holderENorm G.d α (B i) (ζ i))*(∑ j,holderENorm G.d α (B j) f) :=
      mul_le_mul_left le_add_self _

end RothschildStein.S

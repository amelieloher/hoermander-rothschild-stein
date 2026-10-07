-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactLocalLp
public import RothschildStein.S.HolderWeakLocality
public import RothschildStein.S.SobolevCutoffZero
public import RothschildStein.S.SobolevZeroAE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞}

/-- Compactly supported weak Hölder data belong to every weighted Sobolev class on the same domain (BB p. 593). -/
theorem memSobolevX_of_memWeakHolderX_compact
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (k : ℕ) {α : ℝ} (hα : 0 < α)
    {f : (Fin n → ℝ) → ℝ} (hf : memWeakHolderX w X G.d U k α f)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hz : ∀ x ∈ (U : Set (Fin n → ℝ)) \ K,f x = 0) :
    memSobolevX w X U k p f := by
  have hl : MemLp f p (volume.restrict (U : Set (Fin n → ℝ))) :=
    memLp_of_compact_local_support U hK hKU
      ((memWeakHolderX_continuousOn Ω U G hU w X k hα hf).aestronglyMeasurable U.isOpen.measurableSet)
      hz (holderENorm G.d α (U : Set (Fin n → ℝ)) f) hf.1.ne
      (fun x hx => by simpa only [← ofReal_norm,Real.norm_eq_abs] using!
        enorm_le_holderENorm G.d α (U : Set (Fin n → ℝ)) f (hKU hx))
  refine ⟨hl,fun I hI => ?_⟩
  obtain ⟨g,hg,hn⟩ := hf.2 I hI
  refine ⟨g,hg,?_⟩
  exact memLp_of_compact_local_support U hK hKU
    ((continuousOn_of_holderENorm_lt_top_subset Ω G hU hα hn).aestronglyMeasurable U.isOpen.measurableSet)
    (weakHolder_derivative_zero_off_support Ω U G hU X I hα hg hn hK.isClosed hz)
    (holderENorm G.d α (U : Set (Fin n → ℝ)) g) hn.ne
    (fun x hx => by simpa only [← ofReal_norm,Real.norm_eq_abs] using!
      enorm_le_holderENorm G.d α (U : Set (Fin n → ℝ)) g (hKU hx))

/-- Compactly supported weak Hölder data belong to the zero-boundary Sobolev class for every finite p ≥ 1 (BB p. 593; Corollary 2.10, p. 73). -/
theorem memSobolevXZero_of_memWeakHolderX_compact
    [Fact (1 ≤ p)] (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j,ContDiffOn ℝ (⊤ : ℕ∞) (X j) (U : Set (Fin n → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) (hpt : p ≠ ⊤)
    {f : (Fin n → ℝ) → ℝ} (hf : memWeakHolderX w X G.d U k α f)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hz : ∀ x ∈ (U : Set (Fin n → ℝ)) \ K,f x = 0) :
    memSobolevXZero w X U k p f := by
  have hl := memSobolevX_of_memWeakHolderX_compact (p := p) Ω U G hU w X k hα hf hK hKU hz
  obtain ⟨χ,W,hW,hKW,_,hone⟩ := exists_test_plateau U ⟨K,hK⟩ hKU
  have hm := memSobolevXZero_mul_test w X U hX k hpt hl χ
  have he : (fun x => f x*χ x) =ᵐ[volume.restrict (U : Set (Fin n → ℝ))] f := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    by_cases hk : x ∈ K
    · have hc : χ x = 1 := hone (hKW hk)
      rw [hc,mul_one]
    · rw [hz x ⟨hx,hk⟩,zero_mul]
  exact (memSobolevXZero_congr_ae X U w k p he).mp hm

end RothschildStein.S

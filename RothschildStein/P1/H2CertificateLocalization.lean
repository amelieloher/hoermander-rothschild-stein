-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2CertificateGeometry

/-!
# Finite localization: centres, partition of unity and cutoffs

For a compact output support `F` inside the region `Ω₀` of the metric-measure certificate and a
common radius `0 < r < κ` there are finitely many centres `z_j ∈ Ω₀` with
`F ⊆ ⋃ B(z_j, r/4)`, smooth `0 ≤ χ_j, ψ_j ≤ 1` with `∑ χ_j = 1` near `F`,
`supp χ_j ⋐ B(z_j, r/4)`, `ψ_j = 1` on `B(z_j, r/2)` and `supp ψ_j ⋐ B(z_j, r)`
(BB pp. 306–309, 325–327). The cutoffs are
Euclidean-smooth functions on the ambient space `ℝ^{n+m}`; the balls are balls of the carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology Manifold ContDiff
namespace RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

namespace LiftedChart

variable (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The finite localization of a compact set `F`: centres
`z ∈ t ⊆ Ω₀` with `F ⊆ ⋃ B(z, r/4)`, smooth cutoffs `χ_z`, `ψ_z` on `ℝ^{n+m}` with values in
`[0, 1]`, `∑ χ_z = 1` on a neighbourhood `N` of `F` (and `≤ 1` everywhere),
`supp χ_z ⋐ B(z, r/4)`, `ψ_z = 1` on `B(z, r/2)` and `supp ψ_z ⋐ B(z, r)`. -/
structure IsLocalization (S : H2.LocDoubling C.Carrier) (F : Set (Fin (n + m) → ℝ)) (r : ℝ)
    (t : Finset C.Carrier) (χ ψ : C.Carrier → (Fin (n + m) → ℝ) → ℝ) : Prop where
  centers_mem : ∀ z ∈ t, z ∈ S.Ω₀
  cover : F ⊆ ⋃ z ∈ t, Carrier.val '' ball z (r / 4)
  χ_smooth : ∀ z ∈ t, ContDiff ℝ (⊤ : ℕ∞) (χ z)
  ψ_smooth : ∀ z ∈ t, ContDiff ℝ (⊤ : ℕ∞) (ψ z)
  χ_mem : ∀ z ∈ t, ∀ ξ, 0 ≤ χ z ξ ∧ χ z ξ ≤ 1
  ψ_mem : ∀ z ∈ t, ∀ ξ, 0 ≤ ψ z ξ ∧ ψ z ξ ≤ 1
  χ_compact : ∀ z ∈ t, IsCompact (tsupport (χ z))
  χ_support : ∀ z ∈ t, tsupport (χ z) ⊆ Carrier.val '' ball z (r / 4)
  ψ_eq_one : ∀ z ∈ t, ∀ ξ ∈ Carrier.val '' ball z (r / 2), ψ z ξ = 1
  ψ_compact : ∀ z ∈ t, IsCompact (tsupport (ψ z))
  ψ_support : ∀ z ∈ t, tsupport (ψ z) ⊆ Carrier.val '' ball z r
  sum_le_one : ∀ ξ, ∑ z ∈ t, χ z ξ ≤ 1
  sum_eq_one : ∃ N : Set (Fin (n + m) → ℝ), IsOpen N ∧ F ⊆ N ∧ ∀ ξ ∈ N, ∑ z ∈ t, χ z ξ = 1

/-- Closed balls of radius `≤ 6κ` about points of `Ω₀` have compact
image in the ambient space (`closedBall y (6κ) ⊆ Ω₁ ⊆ closure Ω₂`, compact). -/
theorem isCompact_image_closedBall (S : H2.LocDoubling C.Carrier) {z : C.Carrier}
    (hz : z ∈ S.Ω₀) {ρ' : ℝ} (hρ' : ρ' ≤ 6 * S.κ) :
    IsCompact (Carrier.val '' closedBall z ρ' : Set (Fin (n + m) → ℝ)) := by
  refine IsCompact.image ?_ Carrier.continuous_val
  exact S.cpt.of_isClosed_subset isClosed_closedBall
    ((closedBall_subset_closedBall hρ').trans ((S.incl₀ z hz).trans (S.sub₁₂.trans subset_closure)))

/-- The doubled balls `B(z, 2r)`, `z ∈ Ω₀`, `r < κ`, lie in `Ω₁`
together with their `6r`-margins (`closedBall z (6κ) ⊆ Ω₁`). -/
theorem ball_two_mul_subset_Ω₁ (S : H2.LocDoubling C.Carrier) {z : C.Carrier} (hz : z ∈ S.Ω₀)
    {r : ℝ} (hr : r ≤ S.κ) : closedBall z (2 * r) ⊆ S.Ω₁ :=
  (closedBall_subset_closedBall (by linarith [S.κ_pos])).trans (S.incl₀ z hz)

/-- Existence of the finite localization: for every compact
`F ⊆ val '' Ω₀` and every `0 < r < κ` (BB pp. 306–309). -/
theorem exists_localization (S : H2.LocDoubling C.Carrier) {F : Set (Fin (n + m) → ℝ)}
    (hF : IsCompact F) (hFΩ : F ⊆ Carrier.val '' S.Ω₀) {r : ℝ} (hr : 0 < r) (hrκ : r < S.κ) :
    ∃ (t : Finset C.Carrier) (χ ψ : C.Carrier → (Fin (n + m) → ℝ) → ℝ),
      C.IsLocalization S F r t χ ψ := by
  classical
  have hκ := S.κ_pos
  have hFU : F ⊆ C.U := fun ξ hξ => by
    obtain ⟨y, -, rfl⟩ := hFΩ hξ
    exact y.val_mem
  have hFt : IsCompact (Carrier.val ⁻¹' F : Set C.Carrier) := Carrier.isCompact_preimage_val hF hFU
  have hFtΩ : (Carrier.val ⁻¹' F : Set C.Carrier) ⊆ S.Ω₀ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hFΩ hx
    rwa [← Carrier.val_injective hyx]
  -- finite cover by balls of radius `r / 4`
  obtain ⟨T, hTF, hTfin, hcover⟩ := finite_cover_balls_of_compact hFt (e := r / 4) (by positivity)
  set t : Finset C.Carrier := hTfin.toFinset with ht
  have hmem : ∀ z, z ∈ t ↔ z ∈ T := fun z => hTfin.mem_toFinset
  have hcen : ∀ z ∈ t, z ∈ S.Ω₀ := fun z hz => hFtΩ (hTF ((hmem z).mp hz))
  have hcover' : (Carrier.val ⁻¹' F : Set C.Carrier) ⊆ ⋃ z ∈ t, ball z (r / 4) := by
    refine hcover.trans ?_
    intro x hx
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨z, hz, hxz⟩ := hx
    exact ⟨z, (hmem z).mpr hz, hxz⟩
  have hopenU : IsOpen (⋃ z ∈ t, ball z (r / 4) : Set C.Carrier) :=
    isOpen_biUnion fun z _ => isOpen_ball
  obtain ⟨ε, hε, hεsub⟩ := hFt.exists_cthickening_subset_open hopenU hcover'
  -- the thickened set is compact and lies in the union of the balls
  have hballsub : ∀ z ∈ t, ball z (r / 4) ⊆ S.Ω₁ := fun z hz x hx =>
    S.incl₀ z (hcen z hz) (mem_closedBall.mpr (by
      have := mem_ball.mp hx
      linarith))
  have hFc_sub : cthickening ε (Carrier.val ⁻¹' F : Set C.Carrier) ⊆ closure S.Ω₂ := by
    intro x hx
    have := hεsub hx
    simp only [mem_iUnion] at this
    obtain ⟨z, hz, hxz⟩ := this
    exact subset_closure (S.sub₁₂ (hballsub z hz hxz))
  have hFc : IsCompact (cthickening ε (Carrier.val ⁻¹' F : Set C.Carrier)) :=
    S.cpt.of_isClosed_subset isClosed_cthickening hFc_sub
  have hF2 : IsCompact (Carrier.val '' cthickening ε (Carrier.val ⁻¹' F : Set C.Carrier)) :=
    hFc.image Carrier.continuous_val
  -- the partition of unity
  set Uo : C.Carrier → Set (Fin (n + m) → ℝ) :=
    fun i => if i ∈ t then Carrier.val '' ball i (r / 4) else ∅ with hUo
  have hUo_open : ∀ i, IsOpen (Uo i) := by
    intro i
    by_cases hi : i ∈ t
    · simp only [hUo, ite_eq_left hi]
      exact Carrier.isOpenEmbedding_val.isOpenMap _ isOpen_ball
    · simp only [hUo, ite_eq_right hi]
      exact isOpen_empty
  have hUo_cover : Carrier.val '' cthickening ε (Carrier.val ⁻¹' F : Set C.Carrier) ⊆ ⋃ i, Uo i := by
    rintro _ ⟨x, hx, rfl⟩
    have := hεsub hx
    simp only [mem_iUnion] at this
    obtain ⟨z, hz, hxz⟩ := this
    refine mem_iUnion.mpr ⟨z, ?_⟩
    simp only [hUo, ite_eq_left hz]
    exact ⟨x, hxz, rfl⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin (n + m) → ℝ)
    hF2.isClosed Uo hUo_open hUo_cover
  have hf0 : ∀ i, i ∉ t → ∀ ξ, f i ξ = 0 := by
    intro i hi ξ
    by_contra hne
    have h1 : ξ ∈ tsupport (f i) := subset_tsupport _ (Function.mem_support.mpr hne)
    have h2 := hf i h1
    simp only [hUo, ite_eq_right hi] at h2
    exact (Set.mem_empty_iff_false ξ).mp h2
  have hfsum : ∀ ξ, ∑ᶠ i, f i ξ = ∑ i ∈ t, f i ξ := by
    intro ξ
    refine finsum_eq_sum_of_support_subset (fun i => f i ξ) ?_
    intro i hi
    by_contra hnt
    exact hi (hf0 i hnt ξ)
  -- the cutoffs `ψ`
  have hψ : ∀ z : C.Carrier, ∃ ψ : (Fin (n + m) → ℝ) → ℝ, z ∈ t →
      (ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ ξ, 0 ≤ ψ ξ ∧ ψ ξ ≤ 1) ∧
        (∀ ξ ∈ Carrier.val '' ball z (r / 2), ψ ξ = 1) ∧
        IsCompact (tsupport ψ) ∧ tsupport ψ ⊆ Carrier.val '' ball z r) := by
    intro z
    by_cases hz : z ∈ t
    · have hzΩ := hcen z hz
      have hs : IsOpen (Carrier.val '' ball z (3 * r / 4) : Set (Fin (n + m) → ℝ)) :=
        Carrier.isOpenEmbedding_val.isOpenMap _ isOpen_ball
      have hc1 := C.isCompact_image_closedBall S hzΩ (ρ' := r / 2) (by linarith)
      have hc2 := C.isCompact_image_closedBall S hzΩ (ρ' := 3 * r / 4) (by linarith)
      have hts : (Carrier.val '' closedBall z (r / 2) : Set (Fin (n + m) → ℝ)) ⊆
          Carrier.val '' ball z (3 * r / 4) :=
        image_mono (closedBall_subset_ball (by linarith))
      obtain ⟨g, hg, hrange, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
        hs hc1.isClosed hts
      refine ⟨g, fun _ => ⟨hg, fun ξ => ⟨(hrange ⟨ξ, rfl⟩).1, (hrange ⟨ξ, rfl⟩).2⟩, ?_, ?_, ?_⟩⟩
      · intro ξ hξ
        exact (hone ξ).mp (image_mono ball_subset_closedBall hξ)
      · have hsub : tsupport g ⊆ Carrier.val '' closedBall z (3 * r / 4) := by
          rw [tsupport, hsupp]
          exact closure_minimal (image_mono ball_subset_closedBall) hc2.isClosed
        exact hc2.of_isClosed_subset (isClosed_tsupport _) hsub
      · have hsub : tsupport g ⊆ Carrier.val '' closedBall z (3 * r / 4) := by
          rw [tsupport, hsupp]
          exact closure_minimal (image_mono ball_subset_closedBall) hc2.isClosed
        exact hsub.trans (image_mono (closedBall_subset_ball (by linarith)))
    · exact ⟨0, fun h => absurd h hz⟩
  choose ψ hψ using hψ
  refine ⟨t, fun i => (f i : (Fin (n + m) → ℝ) → ℝ), ψ, ?_⟩
  have hχsub : ∀ z ∈ t, tsupport (f z : (Fin (n + m) → ℝ) → ℝ) ⊆
      Carrier.val '' ball z (r / 4) := by
    intro z hz
    have := hf z
    simpa only [hUo, ite_eq_left hz] using this
  exact
    { centers_mem := hcen
      cover := by
        intro ξ hξ
        obtain ⟨y, rfl⟩ : ξ ∈ Set.range (Carrier.val : C.Carrier → Fin (n + m) → ℝ) := by
          rw [Carrier.range_val]; exact hFU hξ
        have := hcover' (show y ∈ Carrier.val ⁻¹' F from hξ)
        simp only [mem_iUnion] at this ⊢
        obtain ⟨z, hz, hyz⟩ := this
        exact ⟨z, hz, y, hyz, rfl⟩
      χ_smooth := fun z _ => contMDiff_iff_contDiff.mp (f z).contMDiff
      ψ_smooth := fun z hz => (hψ z hz).1
      χ_mem := fun z _ ξ => ⟨f.nonneg z ξ, f.le_one z ξ⟩
      ψ_mem := fun z hz => (hψ z hz).2.1
      χ_compact := fun z hz => by
        have hc := C.isCompact_image_closedBall S (hcen z hz) (ρ' := r / 4) (by linarith)
        exact hc.of_isClosed_subset (isClosed_tsupport _)
          ((hχsub z hz).trans (image_mono ball_subset_closedBall))
      χ_support := hχsub
      ψ_eq_one := fun z hz => (hψ z hz).2.2.1
      ψ_compact := fun z hz => (hψ z hz).2.2.2.1
      ψ_support := fun z hz => (hψ z hz).2.2.2.2
      sum_le_one := fun ξ => by
        have h := f.sum_le_one ξ
        rw [hfsum] at h
        exact h
      sum_eq_one := by
        refine ⟨Carrier.val '' thickening ε (Carrier.val ⁻¹' F : Set C.Carrier),
          Carrier.isOpenEmbedding_val.isOpenMap _ isOpen_thickening, ?_, ?_⟩
        · intro ξ hξ
          obtain ⟨y, rfl⟩ : ξ ∈ Set.range (Carrier.val : C.Carrier → Fin (n + m) → ℝ) := by
            rw [Carrier.range_val]; exact hFU hξ
          exact ⟨y, self_subset_thickening hε _ hξ, rfl⟩
        · rintro ξ ⟨y, hy, rfl⟩
          have h := f.sum_eq_one (show Carrier.val y ∈
            Carrier.val '' cthickening ε (Carrier.val ⁻¹' F : Set C.Carrier) from
              ⟨y, thickening_subset_cthickening ε _ hy, rfl⟩)
          rw [hfsum] at h
          exact h }

end LiftedChart

end RothschildStein.P1

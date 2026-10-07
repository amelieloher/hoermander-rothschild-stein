-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ShiftedFamilyGeometry
public import RothschildStein.L1.ZeroShiftFamilyGeometry
public import RothschildStein.L1.MixedWeightedBoxes
public import RothschildStein.G4.ControlTopology
public import RothschildStein.G4.LocalAuxiliary
public import RothschildStein.G1.WeightedTriangle

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped ENNReal Topology
namespace RothschildStein.L1.StarredFiber

/-- The completed frame `(B, J)` with an explicit motive: elaborating
`Fin.addCases B J` without it postpones a higher-order unification that costs
several seconds at every use. The body is the eta-expanded form used by the
completed-frame lemmas (BB pp. 519-520). -/
abbrev completedFrame {q n m s : ℕ} {w : Fin q → ℕ+}
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s) :
    Fin (n + m) → G4.ShortWord w s :=
  fun i => Fin.addCases (motive := fun _ => G4.ShortWord w s) B J i

/-- The conclusion of `JointShortChartFamily.exists_shifted_geometry`
at the shift radius `b`, restricted to the clauses used by the starred fiber
assembly. It is monotone in `b` (BB pp. 520-521). -/
def ShiftedGeometry {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (H : JointShortChartFamily (s := s) w Ω X z t)
    (a b : ℝ) : Prop :=
  ∀ x ∈ closedBall z (H.R/16), ∀ r : ℝ, 0 < r → r ≤ H.r₀ →
    ∀ B : Fin n → G4.ShortWord w s,
    G4.IsSuboptimal (G4.shortField w X) (G4.shortWeight w) B x t r →
    ∀ v ∈ G4.weightedBox (fun j => G4.shortWeight w (G4.shortIndex w j)) (b*r),
    let F := fun u => H.Φ B ((Fin.append u v,x),1)
    let Q := G4.weightedBox (G4.shortWeight w ∘ B) (a*r)
    InjOn F Q ∧
    (∀ u ∈ Q, |G4.frameDet (G4.shortField w X) B x|/4 ≤ |(fderiv ℝ F u).det| ∧
      |(fderiv ℝ F u).det| ≤ 4*|G4.frameDet (G4.shortField w X) B x|) ∧
    ({y | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b*r)} ⊆ F '' Q)

/-- The conclusion of `JointShortChartFamily.exists_zeroShift_geometry`
at the inner radius `b`, restricted to the clauses used by the starred fiber
assembly. It is monotone in `b` (BB pp. 520-521). -/
def ZeroShiftGeometry {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (H : JointShortChartFamily (s := s) w Ω X z t)
    (a b : ℝ) : Prop :=
  ∀ x ∈ closedBall z (H.R/16), ∀ r : ℝ, 0 < r → r ≤ H.r₀ →
    ∀ B : Fin n → G4.ShortWord w s,
    G4.IsSuboptimal (G4.shortField w X) (G4.shortWeight w) B x t r →
    let F := fun u => H.Φ B ((Fin.append u
      (0 : Fin (Fintype.card (G4.ShortWord w s)) → ℝ),x),1)
    let Q := G4.weightedBox (G4.shortWeight w ∘ B) (a*r)
    ContDiffOn ℝ (⊤ : ℕ∞) F Q ∧ InjOn F Q ∧
    (∀ u ∈ Q, |G4.frameDet (G4.shortField w X) B x|/4 ≤ |(fderiv ℝ F u).det| ∧
      |(fderiv ℝ F u).det| ≤ 4*|G4.frameDet (G4.shortField w X) B x|) ∧
    ({y | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b*r)} ⊆ F '' Q) ∧
    (F '' Q ⊆ {y | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (a*r)})

/-- The shifted geometry exists at every permitted horizontal
radius `a`, with the fresh shift radius `b < a/4` (BB pp. 520-521). -/
theorem exists_shiftedGeometry {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (H : JointShortChartFamily (s := s) w Ω X z t)
    {a : ℝ} (ha : 0 < a) (haa₀ : a ≤ H.a₀) :
    ∃ b : ℝ, 0 < b ∧ b < a/4 ∧ ShiftedGeometry H a b := by
  obtain ⟨b,hb,hba,_hb1,hgeo⟩ := H.exists_shifted_geometry ha haa₀
  refine ⟨b,hb,hba,?_⟩
  intro x hx r hr hrr B hB v hv
  obtain ⟨_hsm,_hmaps,hinj,hdet,hinner,_hout⟩ := hgeo x hx r hr hrr B hB v hv
  exact ⟨hinj,hdet,hinner⟩

/-- The zero-shift geometry exists at every permitted horizontal
radius `a`, with the inner radius `b < a/4` (BB pp. 520-521). -/
theorem exists_zeroShiftGeometry {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (H : JointShortChartFamily (s := s) w Ω X z t)
    {a : ℝ} (ha : 0 < a) (haa₀ : a ≤ H.a₀) :
    ∃ b : ℝ, 0 < b ∧ b < a/4 ∧ ZeroShiftGeometry H a b := by
  obtain ⟨b,hb,hba,_hb1,hgeo⟩ := H.exists_zeroShift_geometry ha haa₀
  exact ⟨b,hb,hba,hgeo⟩

/-- Shrinking the shift radius preserves the shifted geometry. -/
theorem ShiftedGeometry.mono {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} {H : JointShortChartFamily (s := s) w Ω X z t}
    {a b b' : ℝ} (h : ShiftedGeometry H a b) (hb' : 0 ≤ b') (hbb : b' ≤ b) :
    ShiftedGeometry H a b' := by
  intro x hx r hr hrr B hB v hv
  have hr' : 0 ≤ b' * r := mul_nonneg hb' hr.le
  have hv' := RothschildStein.L1.weightedBox_subset_of_radius_le
    (fun j => G4.shortWeight w (G4.shortIndex w j)) hr'
    (mul_le_mul_of_nonneg_right hbb hr.le) hv
  obtain ⟨hinj,hdet,hinner⟩ := h x hx r hr hrr B hB v hv'
  refine ⟨hinj,hdet,fun y hy => hinner ?_⟩
  exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbb hr.le))

/-- Shrinking the inner radius preserves the zero-shift geometry. -/
theorem ZeroShiftGeometry.mono {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} {H : JointShortChartFamily (s := s) w Ω X z t}
    {a b b' : ℝ} (h : ZeroShiftGeometry H a b) (hbb : b' ≤ b) :
    ZeroShiftGeometry H a b' := by
  intro x hx r hr hrr B hB
  obtain ⟨hsm,hinj,hdet,hinner,hout⟩ := h x hx r hr hrr B hB
  refine ⟨hsm,hinj,hdet,fun y hy => hinner ?_,hout⟩
  exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbb hr.le))

/-- A positive function on a finite type has a positive common lower bound. -/
theorem exists_pos_le_of_pos {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ a : ℝ, 0 < a ∧ ∀ i, a ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1,one_pos,fun i => (hι.false i).elim⟩
  · obtain ⟨i₀,hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀,hf i₀,hi₀⟩

/-- Auxiliary-distance balls on an open patch with the bracket
condition are Euclidean-open (BB Proposition 9.7, p. 403). -/
theorem isOpen_auxiliaryBall {q n s : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {w : Fin q → ℕ+} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hstep : bracketStepOn Ω w X s)
    (x : Fin n → ℝ) (r : ℝ) :
    IsOpen {y | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyΩ : y ∈ Ω := G4.controlBall_subset_domain Ω
    (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j))
    (fun j => G4.shortField w X (G4.shortIndex (s := s) w j)) x r hy
  obtain ⟨c,hc0,hxc,hcr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hy
  have hcr' : c < r := (ENNReal.ofReal_lt_ofReal_iff'.mp hcr).1
  have hspan : ∃ B : Fin n → Fin (Fintype.card (G4.ShortWord w s)),
      G4.frameDet (fun j => G4.shortField w X (G4.shortIndex (s := s) w j)) B y ≠ 0 := by
    obtain ⟨B,hB⟩ := G4.exists_short_frame hstep hyΩ
    refine ⟨fun i => Fintype.equivFin (G4.ShortWord w s) (B i),?_⟩
    have hmat : G4.frameMatrix (fun j => G4.shortField w X (G4.shortIndex (s := s) w j))
        (fun i => Fintype.equivFin (G4.ShortWord w s) (B i)) y =
        G4.frameMatrix (G4.shortField w X) B y := by
      ext a b
      simp only [G4.frameMatrix, G4.shortIndex, Equiv.symm_apply_apply]
    unfold G4.frameDet
    rw [hmat]
    exact hB
  have hnhds := G4.controlBall_mem_nhds_of_spanning (s := s) hΩ
    (Z := fun j => G4.shortField w X (G4.shortIndex (s := s) w j))
    (fun j => G4.shortField_contDiffOn hΩ hX (G4.shortIndex (s := s) w j))
    (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j))
    (fun j => ((G4.mem_shortWordFamily_iff w (G4.shortIndex (s := s) w j).val).mp
      (G4.shortIndex (s := s) w j).property).2) hyΩ hspan (sub_pos.mpr hcr')
  refine Filter.mem_of_superset hnhds ?_
  intro y' hy'
  have hy'' : controlDistance Ω
      (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j))
      (fun j => G4.shortField w X (G4.shortIndex (s := s) w j)) y y' <
      ENNReal.ofReal (r - c) := hy'
  have htri := G1.controlDistance_triangle Ω
    (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j))
    (fun j => G4.shortField w X (G4.shortIndex (s := s) w j)) x y y'
  have hsum : G4.auxiliaryDistance (s := s) Ω w X x y + ENNReal.ofReal (r - c) <
      ENNReal.ofReal r := by
    calc G4.auxiliaryDistance (s := s) Ω w X x y + ENNReal.ofReal (r - c)
        < ENNReal.ofReal c + ENNReal.ofReal (r - c) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hxc
      _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_add hc0 (sub_nonneg.mpr hcr'.le)]
          congr 1
          ring
  exact (htri.trans (add_le_add le_rfl hy''.le)).trans_lt hsum

end RothschildStein.L1.StarredFiber

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.Definitions.rsBall
public import RothschildStein.G4.ParameterCompactSpatialBallBox
public import RothschildStein.Geometry.CompactFamilyDomainLocalization
public import RothschildStein.Geometry.DistanceComparisonCompactFamily
public import RothschildStein.Definitions.absoluteJacobian
public import RothschildStein.Geometry.BallBoxFrameConversion
public import RothschildStein.Geometry.ContinuousTrajectoryODE
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.Geometry
/-- [GEOM-BB] The revised compact-family ball-box statement (BB Theorem 9.42). -/
theorem exists_ball_box_compact_family
    {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg]
    {k n s : ℕ} (hn : 0 < n)
    (w : Fin (k + 1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω V K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hVΩ : V ⊆ Ω)
    (X : Sg → Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hjoint : ∀ i j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ Ω))
    (hstep : ∀ σ, bracketStepOn V w (X σ) s)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ a b C r₀ : ℝ, 0 < a ∧ 0 < b ∧ 0 < C ∧ 0 < r₀ ∧
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B : Fin n → List (Fin (k + 1)), (∀ j, wordWeight w (B j) ≤ s) →
      (∀ B' : Fin n → List (Fin (k + 1)), (∀ j, wordWeight w (B' j) ≤ s) →
        θ * (|(Matrix.of fun i j => wordBracket (X σ) (B' j) x i).det| *
              r ^ (∑ j, wordWeight w (B' j))) ≤
          |(Matrix.of fun i j => wordBracket (X σ) (B j) x i).det| *
            r ^ (∑ j, wordWeight w (B j))) →
      let Q : Set (Fin n → ℝ) := {u | ∀ j, |u j| < (a * r) ^ wordWeight w (B j)}
      let lam : ℝ := (Matrix.of fun i j => wordBracket (X σ) (B j) x i).det
      ∃ F : (Fin n → ℝ) → (Fin n → ℝ),
        (∀ u ∈ Q, ∃ γ : ℝ → (Fin n → ℝ), γ 0 = x ∧ γ 1 = F u ∧
          ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Ω ∧
            HasDerivWithinAt γ (∑ j, u j • wordBracket (X σ) (B j) (γ t)) (Icc 0 1) t) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) F Q ∧ InjOn F Q ∧
        (∀ u ∈ Q, |lam| / 4 ≤ absoluteJacobian F u ∧ absoluteJacobian F u ≤ 4 * |lam|) ∧
        rsBall Ω w (X σ) x (b * r) ⊆ F '' Q ∧
        F '' Q ⊆ rsBall Ω w (X σ) x (C * r) := by
  classical
  have hs : 1 ≤ s := (w (0 : Fin (k+1))).pos.trans_le (hw 0)
  let m := Fintype.card (G4.ShortWord w s)
  let wf : Fin m → ℕ+ := fun j => G4.shortWeight w (G4.shortIndex w j)
  let Zf : Sg → Fin m → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun σ j => G4.shortField w (X σ) (G4.shortIndex w j)
  have hXV : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) V :=
    fun σ i => (hX σ i).mono hVΩ
  have hjV : ∀ i j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2) (univ ×ˢ V) :=
    fun i j => (hjoint i j).mono (Set.prod_mono Subset.rfl hVΩ)
  let q := n*s+s-1
  let h := q+1
  have horder : q+1 = n*s+s := by dsimp [q]; omega
  obtain ⟨a,b,R,D,κ,ha,ha1,hb,hba,_hb2,hR,hR1,_hD,_hκ,_hκsmall,Φ,hchart⟩ :=
    G4.exists_parameter_compact_spatial_ball_box k n s h q hn (by omega) horder le_rfl
      w V K hV hK hKV X hXV hstep (fun i j _ => hjV i j) θ hθ hθ1
  obtain ⟨Ceq,ε,hCeq,hε,hcomp⟩ :=
    exists_distance_comparison_compact_family hn w hw hV hV hK hKV Subset.rfl
      X hXV hjV hstep
  have hZ : ∀ j, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => Zf z.1 j z.2) (univ ×ˢ Ω) := by
    intro j
    exact (G4.shortField_joint_continuity_of_spatial_jets hΩ w X
      (fun σ _ i => hX σ i) (fun i d _ => hjoint i d) (G4.shortIndex w j)).1
  obtain ⟨εaux,hεaux,hlocal⟩ :=
    exists_compact_family_rsBall_domain_localization hK hV hKV hVΩ wf Zf hZ
  let r₀ := min R (min (ε/(4*a)) (εaux/b))
  have hr₀ : 0 < r₀ := lt_min hR
    (lt_min (div_pos hε (by positivity)) (div_pos hεaux hb))
  refine ⟨a,b,4*Ceq*a,r₀,ha,hb,by positivity,hr₀,?_⟩
  intro σ x hx r hr hrr B hBw hB Q lam
  have hpoint : bracketStepOn {x} w (X σ) s := by
    intro y hy
    have hyx : y = x := mem_singleton_iff.mp hy
    subst y
    exact hstep σ x (hKV hx)
  have hne := ballBox_frame_words_ne_nil w (X σ) hpoint hθ hr B hB
  let Bs : Fin n → G4.ShortWord w s := fun j =>
    ⟨B j,(G4.mem_shortWordFamily_iff w _).mpr ⟨hne j,hBw j⟩⟩
  let Be := (Fintype.equivFin (G4.ShortWord w s)) ∘ Bs
  have hBe : G4.IsSuboptimal (Zf σ) wf Be x θ r :=
    by
      intro C
      have hh := ballBox_frame_suboptimal_shortWords w (X σ) B
        (fun j => ⟨hne j,hBw j⟩) hB (fun j => G4.shortIndex w (C j))
      have hCmat : G4.frameDet (Zf σ) C x =
          G4.frameDet (G4.shortField w (X σ)) (fun j => G4.shortIndex w (C j)) x := rfl
      have hBmat : G4.frameDet (Zf σ) Be x =
          G4.frameDet (G4.shortField w (X σ)) Bs x := by
        apply congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.det)
        funext i j
        change wordBracket (X σ) (G4.shortIndex w (Be j)).val x i =
          wordBracket (X σ) (Bs j).val x i
        simp [G4.shortIndex,Be]
      change θ * (|G4.frameDet (Zf σ) C x| * r ^ G4.frameWeight wf C) ≤ _
      rw [hCmat,hBmat]
      simpa [G4.frameWeight,wf,Be,Bs,G4.shortIndex] using hh
  have hwords : ∀ j, (G4.shortIndex w (Be j)).val = B j := by
    intro j
    simp [G4.shortIndex,Be,Bs]
  have hwQ : Q = G4.weightedBox (wf ∘ Be) (a*r) := by
    ext u
    change (∀ j, |u j| < (a*r) ^ wordWeight w (B j)) ↔
      (∀ j, |u j| < (a*r) ^ wordWeight w (G4.shortIndex w (Be j)).val)
    simp only [hwords]
  let v : Fin m → ℝ := 0
  have hv : v ∈ G4.weightedBox wf (b*r) := by
    intro j
    simp only [v,Pi.zero_apply,abs_zero]
    exact pow_pos (mul_pos hb hr) _
  let F := fun u => Φ x σ Be ((Fin.append u v,x),1)
  have hrR : r ≤ R := hrr.trans (min_le_left _ _)
  have hbr : b*r ≤ εaux := by
    have ht := hrr.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ hb).mp ht
    nlinarith
  have har : 2*a*r < ε := by
    have ht := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 4*a)).mp ht
    nlinarith
  obtain ⟨hAB,htraj,hzero,hinj,hjac,hinner,houter,houteraux,hunshift,hopen,Ψ,hΨ,hΨright,hΨleft,hinverse⟩ :=
    hchart σ x hx r hr hrR Be hBe v hv
  rw [← hwQ] at hAB htraj hinj hjac hinner houter hunshift hopen hΨ hΨright hΨleft hinverse
  have hinnerΩ : rsBall Ω wf (Zf σ) x (b*r) ⊆ F '' Q := by
    rw [hlocal σ x hx (b*r) (mul_pos hb hr) hbr]
    exact fun y hy => hinner hy.2
  have houterV : ∀ y ∈ F '' Q,
      G4.auxiliaryDistance (s := s) V w (X σ) x y < ENNReal.ofReal (2*a*r) :=
    fun y hy => houteraux (houter hy)
  have horiginalInner : rsBall Ω w (X σ) x (b*r) ⊆ F '' Q := by
    intro y hy
    exact hinnerΩ ⟨hy.1,(G4.auxiliaryDistance_le Ω w (X σ) hw x y).trans_lt hy.2⟩
  have horiginalOuter : F '' Q ⊆ rsBall Ω w (X σ) x ((4*Ceq)*a*r) := by
    intro y hy
    have hd := houterV y hy
    have hdε := hd.trans ((ENNReal.ofReal_lt_ofReal_iff hε).mpr har)
    have hc : controlDistance V w (X σ) x y ≤
        ENNReal.ofReal Ceq * G4.auxiliaryDistance (s := s) V w (X σ) x y := by
      simpa only [wordFamily_controlDistance_eq_auxiliaryDistance] using
        (hcomp σ x hx y (by
          simpa only [wordFamily_controlDistance_eq_auxiliaryDistance] using hdε)).2
    have hbnd : controlDistance V w (X σ) x y ≤ ENNReal.ofReal (Ceq*(2*a*r)) := by
      calc
        _ ≤ ENNReal.ofReal Ceq * G4.auxiliaryDistance (s := s) V w (X σ) x y := hc
        _ ≤ ENNReal.ofReal Ceq * ENNReal.ofReal (2*a*r) := mul_le_mul' le_rfl hd.le
        _ = _ := (ENNReal.ofReal_mul hCeq.le).symm
    have hstrict : ENNReal.ofReal (Ceq*(2*a*r)) < ENNReal.ofReal ((4*Ceq)*a*r) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith [mul_pos hCeq (mul_pos ha hr)])
    exact ⟨hVΩ (G4.controlBall_subset_domain V wf (Zf σ) x (2*a*r) hd),
      (G1.controlDistance_mono_domain w (X σ) hVΩ x y).trans hbnd |>.trans_lt hstrict⟩
  have hdet : G4.frameDet (Zf σ) Be x = lam := by
    apply congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.det)
    funext i j
    change wordBracket (X σ) (G4.shortIndex w (Be j)).val x i = wordBracket (X σ) (B j) x i
    rw [hwords]
  have hjacEq : ∀ u, |Matrix.det (G4.coordinateDerivativeMatrix (fderiv ℝ F u))| =
      absoluteJacobian F u := by
    intro u
    rfl
  refine ⟨F,?_,hAB.1,hinj,?_,horiginalInner,?_⟩
  · intro u hu
    obtain ⟨hac,hmap,hstart,hend,hderiv⟩ := htraj u hu
    refine ⟨fun τ => Φ x σ Be ((Fin.append u v,x),τ),hstart,hend,?_⟩
    have hright : ContinuousOn
        (fun t => ∑ j, u j • wordBracket (X σ) (B j) (Φ x σ Be ((Fin.append u v,x),t)))
        (Icc (0 : ℝ) 1) := by
      apply continuousOn_finsetSum
      intro j _
      exact ((G1.wordBracket_contDiffOn hV (X σ) (hXV σ) (B j)).continuousOn.comp
        (by simpa using hac.continuousOn) hmap).const_smul (u j)
    have hd : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), HasDerivAt
        (fun τ => Φ x σ Be ((Fin.append u v,x),τ))
        (∑ j, u j • wordBracket (X σ) (B j) (Φ x σ Be ((Fin.append u v,x),t))) t := by
      filter_upwards [hderiv] with t ht
      simpa [Fin.sum_univ_add,Zf,G4.shortField,hwords,v] using ht
    intro t ht
    exact ⟨hVΩ (hmap ht),trajectory_hasDerivWithinAt hac hright hd t ht⟩
  · intro u hu
    have hh := hjac u hu
    change |G4.frameDet (Zf σ) Be x| / 4 ≤ |Matrix.det (G4.coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
      |Matrix.det (G4.coordinateDerivativeMatrix (fderiv ℝ F u))| ≤ 4 * |G4.frameDet (Zf σ) Be x| at hh
    simpa only [hdet,hjacEq] using hh
  · simpa only [mul_assoc] using horiginalOuter

end RothschildStein.Geometry

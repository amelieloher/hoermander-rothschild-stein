-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderTransfer
public import RothschildStein.P2.TransferCoverHolder

/-!
# Gluing of intrinsic derivatives and the finite cover for the higher Hölder norm

Part of the higher Hölder estimate (BB p. 604: "use the finite-cover argument" of the base Hölder
estimate). The local result
`higher_holder_local_transfer` gives, at every point of the compact `closure Ω'`, a small base ball
`V_ρ(x)` on which `u ∈ C^{k+2,α}_X` with a local estimate. Finitely many balls cover `closure Ω'`; the intrinsic word
derivatives of the cover pieces agree on overlaps (uniqueness) and glue to intrinsic derivatives on `Ω'`
(`hasIntrinsicWordDeriv_glue`), and the Lebesgue number argument (`holderENorm_le_of_cover`) gives
`‖u‖_{C^{k+2,α}(Ω')} ≤ C (‖f‖_{C^{k,α}(Ω'')} + ‖u‖_{L^∞(Ω'')})` (`higher_holder_finite_cover`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

section Glue

variable {n' q : ℕ} {X : Fin q → (Fin n' → ℝ) → (Fin n' → ℝ)}

/-- **Gluing of one-letter intrinsic derivatives.** Intrinsic derivatives `g_i` of the same function `h`
along `Y` on open sets `V_i` (`i` in a finite set `s`) covering `V ⊇ V_i` glue to an intrinsic derivative on `V`. -/
theorem hasIntrinsicDeriv_glue {V : Opens (Fin n' → ℝ)} {ι : Type*} (s : Finset ι)
    (Vi : ι → Opens (Fin n' → ℝ)) (hVi : ∀ i ∈ s, (Vi i : Set (Fin n' → ℝ)) ⊆ (V : Set (Fin n' → ℝ)))
    (hcover : ∀ y ∈ (V : Set (Fin n' → ℝ)), ∃ i ∈ s, y ∈ (Vi i : Set (Fin n' → ℝ)))
    (Y : (Fin n' → ℝ) → (Fin n' → ℝ)) {h : (Fin n' → ℝ) → ℝ} {gi : ι → (Fin n' → ℝ) → ℝ}
    (hd : ∀ i ∈ s, hasIntrinsicDeriv (Vi i) Y h (gi i)) :
    ∃ g : (Fin n' → ℝ) → ℝ, hasIntrinsicDeriv V Y h g ∧
      ∀ i ∈ s, EqOn g (gi i) (Vi i : Set (Fin n' → ℝ)) := by
  classical
  have hcons : ∀ i ∈ s, ∀ i' ∈ s, ∀ y, y ∈ (Vi i : Set (Fin n' → ℝ)) →
      y ∈ (Vi i' : Set (Fin n' → ℝ)) → gi i y = gi i' y := by
    intro i hi i' hi' y hy hy'
    let W : Opens (Fin n' → ℝ) := Vi i ⊓ Vi i'
    have hW1 : (W : Set (Fin n' → ℝ)) ⊆ (Vi i : Set (Fin n' → ℝ)) := fun z hz => hz.1
    have hW2 : (W : Set (Fin n' → ℝ)) ⊆ (Vi i' : Set (Fin n' → ℝ)) := fun z hz => hz.2
    have h1 : hasIntrinsicDeriv W Y h (gi i) := hasIntrinsicDeriv_mono hW1 (hd i hi)
    have h2 : hasIntrinsicDeriv W Y h (gi i') := hasIntrinsicDeriv_mono hW2 (hd i' hi')
    exact S.hasIntrinsicDeriv_unique W Y h1 h2 ⟨hy, hy'⟩
  let g : (Fin n' → ℝ) → ℝ := fun y =>
    if hy : ∃ i ∈ s, y ∈ (Vi i : Set (Fin n' → ℝ)) then gi (Classical.choose hy) y else 0
  have hg : ∀ i ∈ s, EqOn g (gi i) (Vi i : Set (Fin n' → ℝ)) := by
    intro i hi y hy
    have hex : ∃ i ∈ s, y ∈ (Vi i : Set (Fin n' → ℝ)) := ⟨i, hi, hy⟩
    simp only [g, hex, dite_true]
    obtain ⟨hc1, hc2⟩ := Classical.choose_spec hex
    exact hcons _ hc1 i hi y hc2 hy
  refine ⟨g, fun x hx => ?_, hg⟩
  obtain ⟨i, hi, hxi⟩ := hcover x hx
  obtain ⟨⟨γ, h0, hγ, hmem⟩, hall⟩ := hd i hi x hxi
  refine ⟨⟨γ, h0, hγ, hmem.mono fun t ht => hVi i hi ht⟩, fun γ' h0' hγ' hmem' => ?_⟩
  have hcont : ContinuousAt γ' 0 := hγ'.self_of_nhds.continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ' t ∈ (Vi i : Set (Fin n' → ℝ)) :=
    hcont.eventually_mem ((Vi i).isOpen.mem_nhds (by rw [h0']; exact hxi))
  have := hall γ' h0' hγ' hev
  rw [hg i hi hxi]
  exact this

/-- **Gluing of intrinsic word derivatives** (induction on the word). -/
theorem hasIntrinsicWordDeriv_glue {V : Opens (Fin n' → ℝ)} {ι : Type*} (s : Finset ι)
    (Vi : ι → Opens (Fin n' → ℝ)) (hVi : ∀ i ∈ s, (Vi i : Set (Fin n' → ℝ)) ⊆ (V : Set (Fin n' → ℝ)))
    (hcover : ∀ y ∈ (V : Set (Fin n' → ℝ)), ∃ i ∈ s, y ∈ (Vi i : Set (Fin n' → ℝ)))
    {u : (Fin n' → ℝ) → ℝ} {gi : ι → (Fin n' → ℝ) → ℝ} :
    ∀ (I : List (Fin q)), (∀ i ∈ s, hasIntrinsicWordDeriv X (Vi i) I u (gi i)) →
      ∃ g : (Fin n' → ℝ) → ℝ, hasIntrinsicWordDeriv X V I u g ∧
        ∀ i ∈ s, EqOn g (gi i) (Vi i : Set (Fin n' → ℝ))
  | [], h => ⟨u, fun x _ => rfl, fun i hi x hx => (h i hi hx).symm⟩
  | j :: I, h => by
    classical
    have h' : ∀ i ∈ s, ∃ h' : (Fin n' → ℝ) → ℝ, hasIntrinsicWordDeriv X (Vi i) I u h' ∧
        hasIntrinsicDeriv (Vi i) (X j) h' (gi i) := fun i hi => h i hi
    choose! hI hI1 hI2 using h'
    obtain ⟨hg, hg1, hg2⟩ := hasIntrinsicWordDeriv_glue s Vi hVi hcover I hI1
    have hd : ∀ i ∈ s, hasIntrinsicDeriv (Vi i) (X j) hg (gi i) := fun i hi =>
      S.hasIntrinsicDeriv_congr_input (Vi i) (X j) (fun x hx => (hg2 i hi hx).symm) (hI2 i hi)
    obtain ⟨g, hgd, hge⟩ := hasIntrinsicDeriv_glue s Vi hVi hcover (X j) hd
    exact ⟨g, ⟨hg, hg1, hgd⟩, hge⟩

end Glue


section Cover

variable {n q : ℕ} {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}

/-- The local bound at one pair of balls: `u ∈ C^{2,α}_X(V_b)`, `L u = f ∈ C^{k,α}_X(V_b)` give
`u ∈ C^{k+2,α}_X(V_ρ)` with `‖u‖_{C^{k+2,α}(V_ρ)} ≤ K (‖f‖_{C^{k,α}(V_b)} + ‖u‖_{L^∞(V_b)})`. -/
def HigherBoundOn (Ω : Set (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (α : ℝ) (k : ℕ)
    (Vρ Vb : Opens (Fin n → ℝ)) (K : ℝ) : Prop :=
  ∀ u f : (Fin n → ℝ) → ℝ,
    memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vb 2 α u →
    HasIntrinsicOperatorValue X Vb (noDriftOpWords q) u f →
    memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f →
    memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u ∧
    holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u ≤
      ENNReal.ofReal K * (holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f +
        eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ))))

/-- **Gluing and the Lebesgue-number bound for one word**: intrinsic word derivatives `g_x` of `u` on the
sets `A x` of a finite cover of `Ω'` (Lebesgue number `ℓ`), each of Hölder norm at most `M` on `A x`, glue to an
intrinsic word derivative `g` of `u` on `Ω'` with `‖g‖_{C^α(Ω')} ≤ M (2 + 2 ℓ^{-α})`. -/
theorem cover_word_glue {α : ℝ} (hα : 0 < α) {ι : Type} (t : Finset ι) (A : ι → Opens (Fin n → ℝ))
    (Ω' : Opens (Fin n → ℝ)) {ℓ : ℝ} (hℓ0 : 0 < ℓ)
    (hcover : ∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∃ x ∈ t, y ∈ (A x : Set (Fin n → ℝ)))
    (hleb : ∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∀ z ∈ (Ω' : Set (Fin n → ℝ)),
      controlDistance Ω noDriftWeight X y z < ENNReal.ofReal ℓ →
      ∃ x ∈ t, y ∈ (A x : Set (Fin n → ℝ)) ∧ z ∈ (A x : Set (Fin n → ℝ)))
    (hsep : ∀ x ∈ t, ∀ y ∈ (A x : Set (Fin n → ℝ)), ∀ z ∈ (A x : Set (Fin n → ℝ)),
      controlDistance Ω noDriftWeight X y z = 0 → y = z)
    {u : (Fin n → ℝ) → ℝ} (I : List (Fin q)) {gx : ι → (Fin n → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hgx : ∀ x ∈ t, hasIntrinsicWordDeriv X (A x) I u (gx x))
    (hgxb : ∀ x ∈ t, holderENorm (controlDistance Ω noDriftWeight X) α (A x : Set (Fin n → ℝ)) (gx x) ≤
      ENNReal.ofReal M) :
    ∃ g : (Fin n → ℝ) → ℝ, hasIntrinsicWordDeriv X Ω' I u g ∧
      holderENorm (controlDistance Ω noDriftWeight X) α (Ω' : Set (Fin n → ℝ)) g ≤
        ENNReal.ofReal (M * (2 + 2 * (ℓ ^ α)⁻¹)) := by
  classical
  let Vi : ι → Opens (Fin n → ℝ) := fun x => A x ⊓ Ω'
  have hVi : ∀ x ∈ t, ((Vi x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆ (Ω' : Set (Fin n → ℝ)) :=
    fun x _ z hz => hz.2
  have hcov' : ∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∃ x ∈ t,
      y ∈ ((Vi x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) := fun y hy => by
    obtain ⟨x, hxt, hyx⟩ := hcover y hy
    exact ⟨x, hxt, ⟨hyx, hy⟩⟩
  have hVA : ∀ x, ((Vi x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆ (A x : Set (Fin n → ℝ)) :=
    fun x z hz => hz.1
  obtain ⟨g, hg, hgeq⟩ := hasIntrinsicWordDeriv_glue t Vi hVi hcov' I (fun x hx =>
    hasIntrinsicWordDeriv_mono (V := A x) (V' := Vi x) (hVA x) I (hgx x hx))
  refine ⟨g, hg, ?_⟩
  refine holderENorm_le_of_cover (d := controlDistance Ω noDriftWeight X) hα t
    (fun x => ((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) ∩ (Ω' : Set (Fin n → ℝ)))
    (U := (Ω' : Set (Fin n → ℝ))) (g := g) hM hℓ0
    (fun y hy => by
      obtain ⟨x, hxt, hyx⟩ := hcover y hy
      exact ⟨x, hxt, ⟨hyx, hy⟩⟩)
    (fun y hy z hz hyz => by
      obtain ⟨x, hxt, hyx, hzx⟩ := hleb y hy z hz hyz
      exact ⟨x, hxt, ⟨hyx, hy⟩, ⟨hzx, hz⟩⟩)
    (fun x hx y hy z hz hd => hsep x hx y hy.1 z hz.1 hd) (fun x hx => ?_)
  have h1 : holderENorm (controlDistance Ω noDriftWeight X) α
      (((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) ∩ (Ω' : Set (Fin n → ℝ))) g =
      holderENorm (controlDistance Ω noDriftWeight X) α
        (((A x : Opens (Fin n → ℝ)) : Set (Fin n → ℝ)) ∩ (Ω' : Set (Fin n → ℝ))) (gx x) :=
    S.holderENorm_congr _ α _ _ (hgeq x hx)
  rw [h1]
  exact (S.holderENorm_mono _ α _ _ inter_subset_left).trans (hgxb x hx)

/-- **The Lebesgue-number cover of a compact set by half-radius control balls.** -/
theorem cover_lebesgue {S : Set (Fin n → ℝ)} (hS : IsCompact S) (hSΩ : S ⊆ Ω) (ρ : S → ℝ) (hρ0 : ∀ x, 0 < ρ x)
    (hopen : ∀ x : S, IsOpen (rsBall Ω noDriftWeight X x.1 (ρ x / 2))) :
    ∃ (t : Finset S) (ℓ : ℝ), 0 < ℓ ∧
      (∀ y ∈ S, ∃ x ∈ t, y ∈ rsBall Ω noDriftWeight X x.1 (ρ x)) ∧
      (∀ y ∈ S, ∀ z ∈ S, controlDistance Ω noDriftWeight X y z < ENNReal.ofReal ℓ →
        ∃ x ∈ t, y ∈ rsBall Ω noDriftWeight X x.1 (ρ x) ∧ z ∈ rsBall Ω noDriftWeight X x.1 (ρ x)) := by
  classical
  have hnhds : ∀ x (hx : x ∈ S), rsBall Ω noDriftWeight X x (ρ ⟨x, hx⟩ / 2) ∈ 𝓝 x := fun x hx =>
    (hopen ⟨x, hx⟩).mem_nhds ⟨hSΩ hx, by
      rw [G1.controlDistance_self noDriftWeight X (hSΩ hx)]
      exact ENNReal.ofReal_pos.2 (half_pos (hρ0 ⟨x, hx⟩))⟩
  obtain ⟨t, ht⟩ := hS.elim_nhds_subcover' (fun x hx => rsBall Ω noDriftWeight X x (ρ ⟨x, hx⟩ / 2)) hnhds
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_pos_le_finset t (fun x => ρ x / 2) (fun x _ => half_pos (hρ0 x))
  refine ⟨t, ℓ, hℓ0, fun y hy => ?_, fun y hy z hz hyz => ?_⟩
  · have h1 := ht hy
    simp only [mem_iUnion] at h1
    obtain ⟨x, hxt, hyx⟩ := h1
    exact ⟨x, hxt, ⟨hyx.1, lt_of_lt_of_le hyx.2
      (ENNReal.ofReal_le_ofReal (by linarith [hρ0 x]))⟩⟩
  · have h1 := ht hy
    simp only [mem_iUnion] at h1
    obtain ⟨x, hxt, hyx⟩ := h1
    have hρx := hρ0 x
    refine ⟨x, hxt, ⟨hyx.1, lt_of_lt_of_le hyx.2
      (ENNReal.ofReal_le_ofReal (by linarith))⟩, ⟨hSΩ hz, ?_⟩⟩
    calc controlDistance Ω noDriftWeight X x.1 z
        ≤ controlDistance Ω noDriftWeight X x.1 y + controlDistance Ω noDriftWeight X y z :=
          G1.controlDistance_triangle Ω noDriftWeight X x.1 y z
      _ < ENNReal.ofReal (ρ x / 2) + ENNReal.ofReal ℓ := ENNReal.add_lt_add hyx.2 hyz
      _ ≤ ENNReal.ofReal (ρ x / 2) + ENNReal.ofReal (ρ x / 2) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hℓ x hxt))
      _ = ENNReal.ofReal (ρ x) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

/-- From the local statement at every point of `closure Ω'` (for every `ε`), the local statement with
the larger ball inside `Ω''`. -/
theorem cover_refine (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) {α : ℝ} {k : ℕ}
    (Ω' Ω'' : Opens (Fin n → ℝ)) (hΩ'Ω'' : closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)))
    (hΩ''Ω : (Ω'' : Set (Fin n → ℝ)) ⊆ Ω)
    (hloc : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∀ ε : ℝ, 0 < ε →
      ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧ b ≤ ε ∧ 0 < K ∧
        (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω noDriftWeight X x ρ')) ∧
        ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x ρ →
          (Vb : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x b → HigherBoundOn Ω X α k Vρ Vb K) :
    ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧
      rsBall Ω noDriftWeight X x b ⊆ (Ω'' : Set (Fin n → ℝ)) ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω noDriftWeight X x ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x b → HigherBoundOn Ω X α k Vρ Vb K := by
  intro x hx
  obtain ⟨ε, hε0, hεV⟩ := exists_rsBall_subset (w := noDriftWeight) hΩ
    (fun i => (hX i).continuousOn) Ω''.isOpen (hΩ'Ω'' hx) (hΩ''Ω (hΩ'Ω'' hx))
  obtain ⟨ρ, b, K, hρ, hρb, hbε, hK, hopen, hbound⟩ := hloc x hx ε hε0
  exact ⟨ρ, b, K, hρ, hρb, (rsBall_mono Ω noDriftWeight X x hbε).trans hεV, hK, hopen, hbound⟩

/-- **The geometry of the finite cover** of `closure Ω'` by the balls `A x = V_ρ(x)` with the larger balls
`B x = V_b(x) ⊆ Ω''`, a Lebesgue number `ℓ`, separation of the control distance, and the local bounds. -/
theorem cover_geometry (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) {α : ℝ} {k : ℕ}
    (Ω' Ω'' : Opens (Fin n → ℝ)) (hcpt : IsCompact (closure (Ω' : Set (Fin n → ℝ))))
    (hΩ'Ω'' : closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)))
    (hΩ''Ω : (Ω'' : Set (Fin n → ℝ)) ⊆ Ω)
    (hloc' : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧
      rsBall Ω noDriftWeight X x b ⊆ (Ω'' : Set (Fin n → ℝ)) ∧ 0 < K ∧
      (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω noDriftWeight X x ρ')) ∧
      ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x ρ →
        (Vb : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x b → HigherBoundOn Ω X α k Vρ Vb K) :
    ∃ (t : Finset (closure (Ω' : Set (Fin n → ℝ))))
      (A B : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ))
      (K : closure (Ω' : Set (Fin n → ℝ)) → ℝ) (ℓ : ℝ), 0 < ℓ ∧ (∀ x, 0 < K x) ∧
      (∀ x, (B x : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ))) ∧
      (∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∃ x ∈ t, y ∈ (A x : Set (Fin n → ℝ))) ∧
      (∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∀ z ∈ (Ω' : Set (Fin n → ℝ)),
        controlDistance Ω noDriftWeight X y z < ENNReal.ofReal ℓ →
        ∃ x ∈ t, y ∈ (A x : Set (Fin n → ℝ)) ∧ z ∈ (A x : Set (Fin n → ℝ))) ∧
      (∀ x ∈ t, ∀ y ∈ (A x : Set (Fin n → ℝ)), ∀ z ∈ (A x : Set (Fin n → ℝ)),
        controlDistance Ω noDriftWeight X y z = 0 → y = z) ∧
      (∀ x ∈ t, HigherBoundOn Ω X α k (A x) (B x) (K x)) := by
  classical
  have hSΩ : closure (Ω' : Set (Fin n → ℝ)) ⊆ Ω := fun x hx => hΩ''Ω (hΩ'Ω'' hx)
  choose ρ b K hρ0 hρb hbΩ hK0 hopen hbound using hloc'
  obtain ⟨t, ℓ, hℓ0, hcov, hleb⟩ := cover_lebesgue hcpt hSΩ (fun x => ρ x.1 x.2)
    (fun x => hρ0 x.1 x.2) (fun x =>
      hopen x.1 x.2 _ (half_pos (hρ0 x.1 x.2)) (by linarith [hρb x.1 x.2, hρ0 x.1 x.2]))
  let A : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ) := fun x =>
    ⟨rsBall Ω noDriftWeight X x.1 (ρ x.1 x.2), hopen x.1 x.2 _ (hρ0 x.1 x.2) (hρb x.1 x.2)⟩
  let B : closure (Ω' : Set (Fin n → ℝ)) → Opens (Fin n → ℝ) := fun x =>
    ⟨rsBall Ω noDriftWeight X x.1 (b x.1 x.2),
      hopen x.1 x.2 _ ((hρ0 x.1 x.2).trans_le (hρb x.1 x.2)) le_rfl⟩
  refine ⟨t, A, B, fun x => K x.1 x.2, ℓ, hℓ0, fun x => hK0 x.1 x.2, fun x => hbΩ x.1 x.2, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := hcov y (subset_closure hy)
    exact ⟨x, hxt, hyx⟩
  · intro y hy z hz hyz
    obtain ⟨x, hxt, hyx, hzx⟩ := hleb y (subset_closure hy) z (subset_closure hz) hyz
    exact ⟨x, hxt, hyx, hzx⟩
  · intro x _ y hy z _ hd
    have hyΩ : y ∈ Ω := (hy : y ∈ rsBall Ω noDriftWeight X x.1 (ρ x.1 x.2)).1
    exact (G1.controlDistance_eq_zero_iff hΩ noDriftWeight X (fun i => (hX i).continuousOn) hyΩ).1 hd
  · intro x _
    exact hbound x.1 x.2 (A x) (B x) rfl rfl

/-- **From the words to the weighted norm**: if for every word of weight at most `N` the function `u` has an
intrinsic word derivative on `Ω'` of Hölder norm at most `c₀`, and `u` is of finite Hölder norm, then `u` is of class
`C^{N,α}_X(Ω')` with weighted norm at most `|wordFamily N| c₀`. -/
theorem memHolderX_of_words {n' q' : ℕ} {X' : Fin q' → (Fin n' → ℝ) → (Fin n' → ℝ)}
    {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} {Ω' : Opens (Fin n' → ℝ)}
    {u : (Fin n' → ℝ) → ℝ} {N : ℕ} {c₀ : ℝ} (hu : holderENorm d α (Ω' : Set (Fin n' → ℝ)) u < ⊤)
    (hI : ∀ I ∈ wordFamily noDriftWeight N, ∃ g : (Fin n' → ℝ) → ℝ,
      hasIntrinsicWordDeriv X' Ω' I u g ∧ holderENorm d α (Ω' : Set (Fin n' → ℝ)) g ≤ ENNReal.ofReal c₀) :
    memHolderX noDriftWeight X' d Ω' N α u ∧
      holderXENorm noDriftWeight X' d Ω' N α u ≤
        ENNReal.ofReal (((wordFamily (noDriftWeight : Fin q' → ℕ+) N).card : ℝ) * c₀) := by
  choose! gI hgI hgIb using hI
  refine ⟨⟨hu, fun I hI => ⟨gI I, hgI I hI, lt_of_le_of_lt (hgIb I hI) ENNReal.ofReal_lt_top⟩⟩, ?_⟩
  have hcard : ∀ I ∈ wordFamily noDriftWeight N,
      intrinsicWordENorm X' d Ω' I α u ≤ ENNReal.ofReal c₀ := fun I hI => by
    rw [intrinsicWordENorm_eq_holderENorm (hgI I hI)]
    exact hgIb I hI
  calc holderXENorm noDriftWeight X' d Ω' N α u
      = ∑ I ∈ wordFamily noDriftWeight N, intrinsicWordENorm X' d Ω' I α u := rfl
    _ ≤ ∑ _I ∈ wordFamily noDriftWeight N, ENNReal.ofReal c₀ := Finset.sum_le_sum hcard
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- **The cover estimate, abstract form**: with the cover data of `cover_geometry`, if `u` is of finite
Hölder norm on `Ω'` and of class `C^{k+2,α}_X(A x)` with norm at most `L x ≤ L_max` on every `A x` (`x ∈ t`), then
`u` is of class `C^{k+2,α}_X(Ω')` with norm at most `|wordFamily (k+2)| (L_max (2 + 2 ℓ^{-α}))`. -/
theorem cover_apply {α : ℝ} (hα : 0 < α) {k : ℕ} {ι : Type} (t : Finset ι) (A : ι → Opens (Fin n → ℝ))
    (L : ι → ℝ) (Ω' : Opens (Fin n → ℝ)) {ℓ : ℝ} (hℓ0 : 0 < ℓ)
    (hcover : ∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∃ x ∈ t, y ∈ (A x : Set (Fin n → ℝ)))
    (hleb : ∀ y ∈ (Ω' : Set (Fin n → ℝ)), ∀ z ∈ (Ω' : Set (Fin n → ℝ)),
      controlDistance Ω noDriftWeight X y z < ENNReal.ofReal ℓ →
      ∃ x ∈ t, y ∈ (A x : Set (Fin n → ℝ)) ∧ z ∈ (A x : Set (Fin n → ℝ)))
    (hsep : ∀ x ∈ t, ∀ y ∈ (A x : Set (Fin n → ℝ)), ∀ z ∈ (A x : Set (Fin n → ℝ)),
      controlDistance Ω noDriftWeight X y z = 0 → y = z)
    {u : (Fin n → ℝ) → ℝ} {Lmax : ℝ} (hLmax : 0 ≤ Lmax) (hL : ∀ x ∈ t, L x ≤ Lmax)
    (hu : holderENorm (controlDistance Ω noDriftWeight X) α (Ω' : Set (Fin n → ℝ)) u < ⊤)
    (hAloc : ∀ x ∈ t,
      memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u ∧
      holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u ≤
        ENNReal.ofReal (L x)) :
    memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Ω' (k + 2) α u ∧
      holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Ω' (k + 2) α u ≤
        ENNReal.ofReal (((wordFamily (noDriftWeight : Fin q → ℕ+) (k + 2)).card : ℝ) *
          (Lmax * (2 + 2 * (ℓ ^ α)⁻¹))) := by
  classical
  refine memHolderX_of_words hu fun I hI => ?_
  have hlocal : ∀ x ∈ t, ∃ g : (Fin n → ℝ) → ℝ, hasIntrinsicWordDeriv X (A x) I u g := fun x hx => by
    obtain ⟨g, hg, -⟩ := (hAloc x hx).1.2 I hI
    exact ⟨g, hg⟩
  choose! gx hgx using hlocal
  have hgxb : ∀ x ∈ t, holderENorm (controlDistance Ω noDriftWeight X) α (A x : Set (Fin n → ℝ)) (gx x) ≤
      ENNReal.ofReal Lmax := fun x hx => by
    rw [← intrinsicWordENorm_eq_holderENorm (hgx x hx)]
    exact (intrinsicWordENorm_le_holderXENorm noDriftWeight hI u).trans ((hAloc x hx).2.trans
      (ENNReal.ofReal_le_ofReal (hL x hx)))
  exact cover_word_glue hα t A Ω' hℓ0 hcover hleb hsep I hLmax hgx hgxb

/-- **The finite cover for the higher Hölder norm** (BB p. 604; as in the finite cover of the base Hölder estimate). Suppose that at
every point `x` of the compact `closure Ω'` the local statement of `higher_holder_local_transfer` holds for every
`ε > 0`. Then there is `C` such that every `u ∈ C^{2,α}_X(Ω'')` with `L u = f ∈ C^{k,α}_X(Ω'')` lies in
`C^{k+2,α}_X(Ω')` and `‖u‖_{C^{k+2,α}(Ω')} ≤ C (‖f‖_{C^{k,α}(Ω'')} + ‖u‖_{L^∞(Ω'')})`. -/
theorem higher_holder_finite_cover (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {α : ℝ} (hα : 0 < α) {k : ℕ} (Ω' Ω'' : Opens (Fin n → ℝ))
    (hcpt : IsCompact (closure (Ω' : Set (Fin n → ℝ))))
    (hΩ'Ω'' : closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)))
    (hΩ''Ω : (Ω'' : Set (Fin n → ℝ)) ⊆ Ω)
    (hloc : ∀ x ∈ closure (Ω' : Set (Fin n → ℝ)), ∀ ε : ℝ, 0 < ε →
      ∃ ρ b K : ℝ, 0 < ρ ∧ ρ ≤ b ∧ b ≤ ε ∧ 0 < K ∧
        (∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ b → IsOpen (rsBall Ω noDriftWeight X x ρ')) ∧
        ∀ (Vρ Vb : Opens (Fin n → ℝ)), (Vρ : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x ρ →
          (Vb : Set (Fin n → ℝ)) = rsBall Ω noDriftWeight X x b → ∀ u f : (Fin n → ℝ) → ℝ,
          memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vb 2 α u →
          HasIntrinsicOperatorValue X Vb (noDriftOpWords q) u f →
          memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f →
          memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u ∧
          holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vρ (k + 2) α u ≤
            ENNReal.ofReal K * (holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Vb k α f +
              eLpNorm u ⊤ (volume.restrict (Vb : Set (Fin n → ℝ))))) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ u f : (Fin n → ℝ) → ℝ,
      memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Ω'' 2 α u →
      HasIntrinsicOperatorValue X Ω'' (noDriftOpWords q) u f →
      memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Ω'' k α f →
      memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) Ω' (k + 2) α u ∧
      holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Ω' (k + 2) α u ≤
        ENNReal.ofReal Cst * (holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) Ω'' k α f +
          eLpNorm u ⊤ (volume.restrict (Ω'' : Set (Fin n → ℝ)))) := by
  classical
  have hloc' := cover_refine hΩ hX Ω' Ω'' hΩ'Ω'' hΩ''Ω (α := α) (k := k) hloc
  obtain ⟨t, A, B, K, ℓ, hℓ0, hK0, hBΩ, hcover, hleb, hsep, hbound⟩ :=
    cover_geometry hΩ hX Ω' Ω'' hcpt hΩ'Ω'' hΩ''Ω hloc'
  have hΩ'sub : (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) := subset_closure.trans hΩ'Ω''
  obtain ⟨Ksum, hKs1, hKsum⟩ : ∃ Ksum : ℝ, 1 ≤ Ksum ∧ ∀ x ∈ t, K x ≤ Ksum :=
    ⟨1 + ∑ x ∈ t, K x, by linarith [Finset.sum_nonneg fun x (_ : x ∈ t) => (hK0 x).le],
      fun x hx => by
        have := Finset.single_le_sum (f := K) (fun x _ => (hK0 x).le) hx
        linarith⟩
  obtain ⟨cK, hcK⟩ : ∃ cK : ℝ, cK = Ksum * (2 + 2 * (ℓ ^ α)⁻¹) := ⟨_, rfl⟩
  have hℓα : 0 < ℓ ^ α := Real.rpow_pos_of_pos hℓ0 α
  have hcK0 : 0 < cK := by
    rw [hcK]
    have : 0 < Ksum := by linarith
    positivity
  have hCst : 0 < (((wordFamily (noDriftWeight : Fin q → ℕ+) (k + 2)).card : ℝ) + 1) * cK := by
    positivity
  refine ⟨(((wordFamily (noDriftWeight : Fin q → ℕ+) (k + 2)).card : ℝ) + 1) * cK, hCst,
    fun u f hu hf hfk => ?_⟩
  have hu' : holderENorm (controlDistance Ω noDriftWeight X) α (Ω' : Set (Fin n → ℝ)) u < ⊤ :=
    lt_of_le_of_lt (S.holderENorm_mono _ α _ _ hΩ'sub) hu.1
  obtain ⟨N', hN'⟩ : ∃ N' : ℝ≥0∞, N' = holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X)
      Ω'' k α f + eLpNorm u ⊤ (volume.restrict (Ω'' : Set (Fin n → ℝ))) := ⟨_, rfl⟩
  rw [← hN']
  -- the local statements on the cover
  have hAloc : ∀ x ∈ t,
      memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u ∧
      holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u ≤
        ENNReal.ofReal (K x) * N' := fun x hx => by
    obtain ⟨h1, h2⟩ := hbound x hx u f (memHolderX_mono_domain noDriftWeight (hBΩ x) hu)
      (hf.mono (hBΩ x)) (memHolderX_mono_domain noDriftWeight (hBΩ x) hfk)
    rw [hN']
    exact ⟨h1, h2.trans (mul_le_mul' le_rfl (add_le_add
      (holderXENorm_mono_domain noDriftWeight (hBΩ x) k f)
      (eLpNorm_mono_measure _ (Measure.restrict_mono (hBΩ x) le_rfl))))⟩
  by_cases hNtop : N' = ⊤
  · -- the right-hand side is infinite; the regularity follows from the finite local norms
    refine ⟨?_, ?_⟩
    · have hfinx : ∀ x ∈ t,
          holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u ≠ ⊤ :=
        fun x hx => (holderXENorm_lt_top_of_memHolderX (hAloc x hx).1).ne
      exact (cover_apply hα t A (fun x => (holderXENorm noDriftWeight X
          (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u).toReal) Ω' hℓ0 hcover hleb hsep
        (Lmax := ∑ x ∈ t, (holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) (A x)
          (k + 2) α u).toReal)
        (Finset.sum_nonneg fun x _ => ENNReal.toReal_nonneg)
        (fun x hx => Finset.single_le_sum (f := fun x => (holderXENorm noDriftWeight X
          (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) hx)
        hu' (fun x hx => ⟨(hAloc x hx).1, (ENNReal.ofReal_toReal (hfinx x hx)).ge⟩)).1
    · rw [hNtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCst).ne']
      exact le_top
  · obtain ⟨M₀, hM₀, hN'eq⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ N' = ENNReal.ofReal M₀ :=
      ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hNtop).symm⟩
    have hAloc' : ∀ x ∈ t,
        memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u ∧
        holderXENorm noDriftWeight X (controlDistance Ω noDriftWeight X) (A x) (k + 2) α u ≤
          ENNReal.ofReal (K x * M₀) := fun x hx =>
      ⟨(hAloc x hx).1, (hAloc x hx).2.trans (le_of_eq (by
        rw [hN'eq, ← ENNReal.ofReal_mul (hK0 x).le]))⟩
    obtain ⟨hmem, hle⟩ := cover_apply hα t A (fun x => K x * M₀) Ω' hℓ0 hcover hleb hsep
      (Lmax := Ksum * M₀) (mul_nonneg (by linarith) hM₀)
      (fun x hx => mul_le_mul_of_nonneg_right (hKsum x hx) hM₀) hu' hAloc'
    refine ⟨hmem, hle.trans ?_⟩
    have heq : Ksum * M₀ * (2 + 2 * (ℓ ^ α)⁻¹) = cK * M₀ := by
      rw [hcK]
      ring
    rw [heq, hN'eq, ← ENNReal.ofReal_mul hCst.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 0 ≤ cK * M₀ := mul_nonneg hcK0.le hM₀
    nlinarith

end Cover

end RothschildStein.P2.HigherHolder

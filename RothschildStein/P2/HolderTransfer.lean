-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransferReverse
public import RothschildStein.S.IntrinsicUniqueness

/-!
# Hölder transfer (BB Thm 11.54, Def 11.55, Prop 11.56, (11.88)-(11.91), pp. 597-599)

For a lift `f̃ = f ∘ π` on a chart (`LiftedChart`), `0 < t < s < R`, and `δ` the fiber constant of
`C.ball_bounds` (the `δ₀` of the fiber volume bounds):

* forward (`holderTransfer_forward`): `‖f̃‖_{C^{j,α}_{X̃}(U_R)} ≤ ‖f‖_{C^{j,α}_X(V_R)}`;
* reverse (`holderTransfer_reverse_of_doubling`, assuming local doubling of the original balls):
  `‖f‖_{C^α(V_{δ t})} ≤ C ‖f̃‖_{C^α(U_s)}` through the lifted oscillation bound and H2's Campanato
  converse; the same for every `X_I f` that exists, hence for each fixed weighted `C^{j,α}` norm
  (`holderTransfer_reverse_words`);
* continuity (`holderTransfer_continuity_identification_of_doubling`): `f` is continuous on the
  centre set and equal there to the Campanato (Hölder) representative `f*`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k m : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ}

/-- Restriction of an intrinsic derivative to a smaller open set. -/
theorem hasIntrinsicDeriv_mono {Fn : ℕ} {V V' : Opens (Fin Fn → ℝ)}
    (hV : (V' : Set (Fin Fn → ℝ)) ⊆ V) {Y : (Fin Fn → ℝ) → (Fin Fn → ℝ)} {f g : (Fin Fn → ℝ) → ℝ}
    (h : hasIntrinsicDeriv V Y f g) : hasIntrinsicDeriv V' Y f g := by
  intro x hx
  obtain ⟨⟨γ, h0, hγ, hmem⟩, hall⟩ := h x (hV hx)
  refine ⟨⟨γ, h0, hγ, ?_⟩, fun γ' h0' hγ' hmem' =>
    hall γ' h0' hγ' (hmem'.mono fun t ht => hV ht)⟩
  have hcont : ContinuousAt γ 0 := hγ.self_of_nhds.continuousAt
  exact hcont.eventually_mem (V'.isOpen.mem_nhds (by rw [h0]; exact hx))

/-- Restriction of an intrinsic word derivative to a smaller open set. -/
theorem hasIntrinsicWordDeriv_mono {Fn q : ℕ} {V V' : Opens (Fin Fn → ℝ)}
    (hV : (V' : Set (Fin Fn → ℝ)) ⊆ V) {Y : Fin q → (Fin Fn → ℝ) → (Fin Fn → ℝ)} :
    ∀ (I : List (Fin q)) {f g : (Fin Fn → ℝ) → ℝ}, hasIntrinsicWordDeriv Y V I f g →
      hasIntrinsicWordDeriv Y V' I f g
  | [], _, _, h => fun _ hx => h (hV hx)
  | _ :: I, _, _, ⟨h', h1, h2⟩ =>
      ⟨h', hasIntrinsicWordDeriv_mono hV I h1, hasIntrinsicDeriv_mono hV h2⟩

/-- The Hölder norm depends only on the values on the set. -/
theorem holderENorm_congr {Fn : ℕ} {d : (Fin Fn → ℝ) → (Fin Fn → ℝ) → ℝ≥0∞} {α : ℝ}
    {V : Set (Fin Fn → ℝ)} {g g' : (Fin Fn → ℝ) → ℝ} (h : EqOn g g' V) :
    holderENorm d α V g = holderENorm d α V g' := by
  unfold holderENorm holderSeminorm
  congr 1
  · exact iSup_congr fun x => by rw [h x.2]
  · congr 1
    ext C
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hC, hall⟩
      refine ⟨hC, fun x hx y hy hxy => ?_⟩
      rw [← h hx, ← h hy]
      exact hall x hx y hy hxy
    · rintro ⟨hC, hall⟩
      refine ⟨hC, fun x hx y hy hxy => ?_⟩
      rw [h hx, h hy]
      exact hall x hx y hy hxy

/-- If `X_I f = g` on `Vo` then the intrinsic `C^α` norm of `X̃_I f̃`
over `Uo` is exactly the Hölder norm of `g ∘ π` (the lifted derivative is unique). -/
theorem intrinsicWordENorm_eq_of_lift (Uo : Opens (Fin (n + m) → ℝ)) (Vo : Opens (Fin n → ℝ))
    (hproj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ)))
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X (P := P) i) (Uo : Set (Fin (n + m) → ℝ)))
    (d' : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ≥0∞) {α : ℝ} (I : List (Fin k))
    {f g : (Fin n → ℝ) → ℝ} (hg : hasIntrinsicWordDeriv X Vo I f g) :
    intrinsicWordENorm (triangularLift X P) d' Uo I α (fun ξ => f (basePoint ξ)) =
      holderENorm d' α (Uo : Set (Fin (n + m) → ℝ)) (fun ξ => g (basePoint ξ)) := by
  have hlift := hasIntrinsicWordDeriv_comp_basePoint (P := P) Uo Vo hproj hXt I hg
  unfold intrinsicWordENorm
  refine le_antisymm (sInf_le ⟨_, hlift, rfl⟩) (le_sInf ?_)
  rintro r ⟨g', hg', rfl⟩
  have huniq := RothschildStein.S.hasIntrinsicWordDeriv_unique Uo (triangularLift X P) I hg' hlift
  exact (holderENorm_congr huniq).ge

/-- Reverse inequality for the weighted norms: if the intrinsic
derivatives `X_I f`, `I ∈ wordFamily w j`, exist on `V_s` (so that the lift identity
`X̃_I f̃ = (X_I f) ∘ π` of the lifted norm transfer holds on `U_s`), then the function-level reverse inequality `hrev`
(with its constant) applied to each `X_I f` gives
`‖f‖_{C^{j,α}_X(V_{δ t})} ≤ C ‖f̃‖_{C^{j,α}_{X̃}(U_s)}`. -/
theorem holderTransfer_reverse_words (C : LiftedChart w st Ω hΩ X x₀ m) {α : ℝ}
    {η : Fin (n + m) → ℝ} {t s δ Cst : ℝ} (hδts : δ * t ≤ s)
    (hrev : ∀ g : (Fin n → ℝ) → ℝ,
      holderENorm (controlDistance Ω w X) α (rsBall Ω w X (basePoint η) (δ * t)) g ≤
        ENNReal.ofReal Cst *
          holderENorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => g (basePoint ξ)))
    (Vδ Vs : Opens (Fin n → ℝ)) (Us : Opens (Fin (n + m) → ℝ))
    (hVδ : (Vδ : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) (δ * t))
    (hVs : (Vs : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) s)
    (hUs : (Us : Set (Fin (n + m) → ℝ)) = rsBall C.O w C.Xl η s) (j : ℕ)
    {f : (Fin n → ℝ) → ℝ} (hderiv : ∀ I ∈ wordFamily w j, ∃ g, hasIntrinsicWordDeriv X Vs I f g) :
    holderXENorm w X (controlDistance Ω w X) Vδ j α f ≤
      ENNReal.ofReal Cst *
        holderXENorm w C.Xl C.dl Us j α (fun ξ => f (basePoint ξ)) := by
  have hUO : (Us : Set (Fin (n + m) → ℝ)) ⊆ C.O := by
    rw [hUs]
    exact fun ξ hξ => hξ.1
  have hproj : ∀ ξ ∈ (Us : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vs : Set (Fin n → ℝ)) := by
    intro ξ hξ
    rw [hVs]
    exact basePoint_mem_rsBall (P := C.P) (hUs ▸ hξ)
  have hVδVs : (Vδ : Set (Fin n → ℝ)) ⊆ (Vs : Set (Fin n → ℝ)) := by
    rw [hVδ, hVs]
    exact rsBall_mono Ω w X _ hδts
  have hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (Us : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.lift_smooth i).mono hUO
  unfold holderXENorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun I hI => ?_
  obtain ⟨g, hg⟩ := hderiv I hI
  have hgδ : hasIntrinsicWordDeriv X Vδ I f g := hasIntrinsicWordDeriv_mono hVδVs I hg
  have heq := intrinsicWordENorm_eq_of_lift (P := C.P) Us Vs hproj hXt C.dl (α := α) I hg
  calc intrinsicWordENorm X (controlDistance Ω w X) Vδ I α f
      ≤ holderENorm (controlDistance Ω w X) α (Vδ : Set (Fin n → ℝ)) g :=
        sInf_le ⟨g, hgδ, rfl⟩
    _ ≤ ENNReal.ofReal Cst *
          holderENorm C.dl α (Us : Set (Fin (n + m) → ℝ)) (fun ξ => g (basePoint ξ)) := by
        rw [hVδ, hUs]
        exact hrev g
    _ = ENNReal.ofReal Cst * intrinsicWordENorm C.Xl C.dl Us I α (fun ξ => f (basePoint ξ)) := by
        rw [heq]

/-- Hölder transfer (BB Thm 11.54, Def 11.55, Prop 11.56, pp. 597-599), assuming the
original local doubling (`OriginalLocalDoubling`).

(1) forward: for every centre `η`, radius `R`, order `j`, exponent `α ≥ 0` and `f`,
`‖f̃‖_{C^{j,α}_{X̃}(U_R)} ≤ ‖f‖_{C^{j,α}_X(V_R)}`, with `U_R = B̃(η, R)`, `V_R = B(π η, R)`.

(2) reverse: with `δ` the fiber constant of the chart (`δ₀`), for `0 < t < s < r_*` there is `C > 0`
such that for every `η ∈ K`: `‖f‖_{C^α(V_{δ t})} ≤ C ‖f̃‖_{C^α(U_s)}` for every `f`, and the same
bound for the weighted norms `‖·‖_{C^{j,α}}` whenever the derivatives `X_I f`, `|I| ≤ j`, exist on
`V_s`. -/
theorem holderTransfer_of_doubling (C : LiftedChart w st Ω hΩ X x₀ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (hdbl : OriginalLocalDoubling Ω w X (basePoint '' C.U)) :
    (∀ (η : Fin (n + m) → ℝ) (R : ℝ) (Vr : Opens (Fin n → ℝ)) (Ur : Opens (Fin (n + m) → ℝ)),
        (Vr : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) R →
        (Ur : Set (Fin (n + m) → ℝ)) = rsBall C.O w C.Xl η R → ∀ (j : ℕ) (f : (Fin n → ℝ) → ℝ),
        holderXENorm w C.Xl C.dl Ur j α (fun ξ => f (basePoint ξ)) ≤
          holderXENorm w X (controlDistance Ω w X) Vr j α f) ∧
    ∃ rstar δ : ℝ, 0 < rstar ∧ 0 < δ ∧ δ < 1 ∧ ∀ t s : ℝ, 0 < t → t < s → s < rstar →
      ∃ Cst : ℝ, 0 < Cst ∧ ∀ η ∈ K,
        (∀ f : (Fin n → ℝ) → ℝ,
          holderENorm (controlDistance Ω w X) α (rsBall Ω w X (basePoint η) (δ * t)) f ≤
            ENNReal.ofReal Cst *
              holderENorm C.dl α (rsBall C.O w C.Xl η s) (fun ξ => f (basePoint ξ))) ∧
        ∀ (Vδ Vs : Opens (Fin n → ℝ)) (Us : Opens (Fin (n + m) → ℝ)),
          (Vδ : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) (δ * t) →
          (Vs : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) s →
          (Us : Set (Fin (n + m) → ℝ)) = rsBall C.O w C.Xl η s → ∀ (j : ℕ) (f : (Fin n → ℝ) → ℝ),
          (∀ I ∈ wordFamily w j, ∃ g, hasIntrinsicWordDeriv X Vs I f g) →
          holderXENorm w X (controlDistance Ω w X) Vδ j α f ≤
            ENNReal.ofReal Cst *
              holderXENorm w C.Xl C.dl Us j α (fun ξ => f (basePoint ξ)) := by
  refine ⟨fun η R Vr Ur hVr hUr j f => holderTransfer_forward C hα.le η R Vr Ur hVr hUr j f, ?_⟩
  obtain ⟨rstar, δ, hr, hδ0, hδ1, hP⟩ := holderTransfer_reverse_of_doubling C hα hα1 hK hKU hdbl
  refine ⟨rstar, δ, hr, hδ0, hδ1, fun t s ht hts hs => ?_⟩
  obtain ⟨Cst, hCst, hC⟩ := hP t s ht hts hs
  refine ⟨Cst, hCst, fun η hη => ⟨hC η hη, fun Vδ Vs Us hVδ hVs hUs j f hderiv => ?_⟩⟩
  exact holderTransfer_reverse_words C (η := η) (t := t) (s := s) (δ := δ) (Cst := Cst)
    (by nlinarith) (hC η hη) Vδ Vs Us hVδ hVs hUs j hderiv

end RothschildStein.P2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Defs.LieWordEval
public import Hormander.Defs.LieWordLength
public import Hormander.F.WordLocality
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

noncomputable section

open Filter Function Set Topology

namespace Hormander.C

/-- A standard word, written as a generator followed by a
right-nested word. -/
inductive NestedWord (k : ℕ) where
  | generator : Fin (k + 1) → NestedWord k
  | bracket : Fin (k + 1) → NestedWord k → NestedWord k

/-- Ordinary generator-leaf count of a nested word. -/
def nestedLength {k : ℕ} : NestedWord k → ℕ
  | .generator _ => 1
  | .bracket _ w => nestedLength w + 1

/-- Evaluation of a standard word on vector fields. -/
def nestedEval {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin (k + 1) → E → E) : NestedWord k → E → E
  | .generator i => X i
  | .bracket i w => VectorField.lieBracket ℝ (X i) (nestedEval X w)

/-- The finite integer combinations used in the normalization. -/
abbrev WordCombination (k : ℕ) := List (ℤ × NestedWord k)

/-- A finite integer linear combination of standard words. -/
def combinationEval {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin (k + 1) → E → E) : WordCombination k → E → E
  | [] => 0
  | (n, w) :: rest => fun x => (n : ℝ) • nestedEval X w x + combinationEval X rest x

/-- A smooth cutoff supported in an open set makes a locally smooth vector field globally
smooth after multiplication. -/
theorem localized_smul_smooth {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [T2Space E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Set E} (hΩ : IsOpen Ω)
    (φ : E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hK : tsupport φ ⊆ Ω)
    (h : E → F) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x • h x) := by
  rw [← contDiffOn_univ]
  apply isOpen_univ.contDiffOn_iff.mpr
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · exact hφ.contDiffAt.smul (hh.contDiffAt (hΩ.mem_nhds hxΩ))
  · have hxK : x ∉ tsupport φ := fun hxK => hxΩ (hK hxK)
    have hφzero : φ =ᶠ[𝓝 x] fun _ => 0 :=
      (notMem_tsupport_iff_eventuallyEq).mp hxK
    have hzero : (fun y => φ y • h y) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [hφzero] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- Standard nested words evaluated from two field families agreeing on an open set agree
there. Their ambient derivatives are determined by those local values. -/
theorem nestedEval_eqOn_of_eqOn {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W : Set E} (hW : IsOpen W)
    (X Y : Fin (k + 1) → E → E) (hXY : ∀ i, EqOn (X i) (Y i) W) :
    ∀ w : NestedWord k, EqOn (nestedEval X w) (nestedEval Y w) W := by
  intro w
  induction w with
  | generator i => exact hXY i
  | bracket i w ih =>
      intro x hx
      have hiNear : X i =ᶠ[𝓝 x] Y i := by
        filter_upwards [hW.mem_nhds hx] with y hy
        exact hXY i hy
      have hwNear : nestedEval X w =ᶠ[𝓝 x] nestedEval Y w := by
        filter_upwards [hW.mem_nhds hx] with y hy
        exact ih hy
      have hiDeriv := hiNear.fderiv_eq (𝕜 := ℝ)
      have hwDeriv := hwNear.fderiv_eq (𝕜 := ℝ)
      change VectorField.lieBracket ℝ (X i) (nestedEval X w) x =
        VectorField.lieBracket ℝ (Y i) (nestedEval Y w) x
      change fderiv ℝ (nestedEval X w) x (X i x) -
          fderiv ℝ (X i) x (nestedEval X w x) =
        fderiv ℝ (nestedEval Y w) x (Y i x) -
          fderiv ℝ (Y i) x (nestedEval Y w x)
      rw [hwDeriv, hiDeriv, hXY i hx, ih hx]

/-- Finite integer combinations of standard words preserve equality of the generators on an
open set. -/
theorem combinationEval_eqOn_of_eqOn {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W : Set E} (hW : IsOpen W)
    (X Y : Fin (k + 1) → E → E) (hXY : ∀ i, EqOn (X i) (Y i) W) :
    ∀ c : WordCombination k, EqOn (combinationEval X c) (combinationEval Y c) W := by
  intro c
  induction c with
  | nil => intro x hx; simp [combinationEval]
  | cons head c ih =>
      rcases head with ⟨n, w⟩
      intro x hx
      simp only [combinationEval]
      rw [nestedEval_eqOn_of_eqOn hW X Y hXY w hx, ih hx]

/-- Put one fixed generator outside every word in a combination. -/
def raiseOuter {k : ℕ} (i : Fin (k + 1)) (c : WordCombination k) : WordCombination k :=
  c.map fun z => (z.1, .bracket i z.2)

/-- Negate every integer coefficient in a combination. -/
def negateCombination {k : ℕ} (c : WordCombination k) : WordCombination k :=
  c.map fun z => (-z.1, z.2)

/-- Nested words made from smooth generators remain smooth. -/
theorem nestedEval_contDiff {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin (k + 1) → E → E) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) :
    ∀ w : NestedWord k, ContDiff ℝ (⊤ : ℕ∞) (nestedEval X w) := by
  intro w
  induction w with
  | generator i => exact hX i
  | bracket i w ih =>
      exact (hX i).lieBracket_vectorField ih (by simp)

theorem combinationEval_contDiff {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) :
    ∀ c : WordCombination k, ContDiff ℝ (⊤ : ℕ∞) (combinationEval X c) := by
  intro c
  induction c with
  | nil => exact contDiff_const
  | cons head rest ih =>
      rcases head with ⟨n, w⟩
      simp only [combinationEval]
      exact (ContDiff.const_smul (n : ℝ) (nestedEval_contDiff X hX w)).add ih

/-- Evaluation respects concatenation of combinations. -/
theorem combinationEval_append {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E) (p q : WordCombination k) :
    combinationEval X (p ++ q) = combinationEval X p + combinationEval X q := by
  induction p with
  | nil => simp [combinationEval]
  | cons head p ih =>
      rcases head with ⟨n, w⟩
      funext x
      simp [combinationEval, ih, add_assoc]

/-- Evaluation respects negation of combinations. -/
theorem combinationEval_negate {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E) (c : WordCombination k) :
    combinationEval X (negateCombination c) = - combinationEval X c := by
  induction c with
  | nil => simp [negateCombination, combinationEval]
  | cons head c ih =>
      rcases head with ⟨n, w⟩
      funext x
      simp only [negateCombination, List.map_cons, combinationEval, Int.cast_neg]
      have ih' : combinationEval X (List.map (fun z => (-z.1, z.2)) c) =
          -combinationEval X c := by
        simpa only [negateCombination] using ih
      rw [ih']
      simp only [Pi.neg_apply]
      simp only [neg_smul]
      rw [← neg_add]

/-- Bracketing a combination by a generator distributes. -/
theorem combinationEval_raiseOuter {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (i : Fin (k + 1))
    (c : WordCombination k) :
    combinationEval X (raiseOuter i c) =
      VectorField.lieBracket ℝ (X i) (combinationEval X c) := by
  induction c with
  | nil =>
      funext x
      simp [raiseOuter, combinationEval, VectorField.lieBracket]
  | cons head c ih =>
      rcases head with ⟨n, w⟩
      funext x
      have hw : DifferentiableAt ℝ (nestedEval X w) x :=
        (nestedEval_contDiff X hX w).differentiable (by simp) x
      have hc : DifferentiableAt ℝ (combinationEval X c) x :=
        (combinationEval_contDiff X hX c).differentiable (by simp) x
      have hscaled : DifferentiableAt ℝ (fun y => (n : ℝ) • nestedEval X w y) x :=
        hw.const_smul (n : ℝ)
      change (n : ℝ) • nestedEval X (.bracket i w) x +
          combinationEval X (raiseOuter i c) x =
        VectorField.lieBracket ℝ (X i)
          ((fun y => (n : ℝ) • nestedEval X w y) + combinationEval X c) x
      rw [VectorField.lieBracket_add_right hscaled hc]
      have hsmul : VectorField.lieBracket ℝ (X i)
          (fun y => (n : ℝ) • nestedEval X w y) x =
          (n : ℝ) • VectorField.lieBracket ℝ (X i) (nestedEval X w) x := by
        change VectorField.lieBracket ℝ (X i)
          ((n : ℝ) • nestedEval X w) x = _
        exact VectorField.lieBracket_const_smul_right
          (V := X i) (W := nestedEval X w) (c := (n : ℝ)) hw
      rw [hsmul, ih]
      simp only [nestedEval]

/-- Jacobi recursively expands a bracket into standard words. -/
def bracketExpansion {k : ℕ} : NestedWord k → NestedWord k → WordCombination k
  | .generator i, w => [(1, .bracket i w)]
  | .bracket i u, w =>
      raiseOuter i (bracketExpansion u w) ++
        negateCombination (bracketExpansion u (.bracket i w))
termination_by u _ => nestedLength u
decreasing_by
  all_goals
    simp [nestedLength]

/-- Raising the outer generator adds one leaf to each word. -/
theorem raiseOuter_length {k : ℕ} (i : Fin (k + 1)) (c : WordCombination k)
    (m : ℕ) (hm : ∀ z ∈ c, nestedLength z.2 = m) :
    ∀ z ∈ raiseOuter i c, nestedLength z.2 = m + 1 := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨p, hp, hpz⟩
  rcases p with ⟨n, w⟩
  cases hpz
  simp [nestedLength, hm (n, w) hp]

/-- Negation preserves the lengths in a combination. -/
theorem negateCombination_length {k : ℕ} (c : WordCombination k) (m : ℕ)
    (hm : ∀ z ∈ c, nestedLength z.2 = m) :
    ∀ z ∈ negateCombination c, nestedLength z.2 = m := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨p, hp, hpz⟩
  rcases p with ⟨n, w⟩
  cases hpz
  exact hm (n, w) hp

/-- Every word in the Jacobi expansion has the summed length. -/
theorem bracketExpansion_length {k : ℕ} (u w : NestedWord k) :
    ∀ z ∈ bracketExpansion u w, nestedLength z.2 = nestedLength u + nestedLength w := by
  revert w
  induction u with
  | generator i =>
      intro w z hz
      simp only [bracketExpansion, List.mem_singleton] at hz
      cases hz
      simp [nestedLength]
      omega
  | bracket i u ih =>
      intro w z hz
      have hz' : z ∈ raiseOuter i (bracketExpansion u w) ∨
          z ∈ negateCombination (bracketExpansion u (.bracket i w)) := by
        simpa [bracketExpansion, List.mem_append] using hz
      rcases hz' with hleft | hright
      · have h := raiseOuter_length i (bracketExpansion u w)
          (nestedLength u + nestedLength w) (ih w) z hleft
        simp only [nestedLength] at h ⊢
        omega
      · have h := negateCombination_length (bracketExpansion u (.bracket i w))
          (nestedLength u + nestedLength (.bracket i w)) (ih (.bracket i w)) z hright
        simp only [nestedLength] at h ⊢
        omega

/-- Evaluation of the recursive Jacobi expansion is the bracket. -/
theorem bracketExpansion_eval {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u w : NestedWord k) :
      combinationEval X (bracketExpansion u w) =
      VectorField.lieBracket ℝ (nestedEval X u) (nestedEval X w) := by
  revert w
  induction u with
  | generator i =>
      intro w
      funext x
      simp [bracketExpansion, combinationEval, nestedEval]
  | bracket i u ih =>
      intro w
      funext x
      simp only [bracketExpansion]
      rw [combinationEval_append]
      rw [combinationEval_raiseOuter X hX i]
      rw [combinationEval_negate]
      rw [ih w, ih (.bracket i w)]
      have hXi : ContDiffAt ℝ (2 : WithTop ℕ∞) (X i) x :=
        ((hX i).contDiffAt).of_le (by norm_num)
      have hU : ContDiffAt ℝ (2 : WithTop ℕ∞) (nestedEval X u) x :=
        ((nestedEval_contDiff X hX u).contDiffAt).of_le (by norm_num)
      have hW : ContDiffAt ℝ (2 : WithTop ℕ∞) (nestedEval X w) x :=
        ((nestedEval_contDiff X hX w).contDiffAt).of_le (by norm_num)
      have hJacobi := VectorField.leibniz_identity_lieBracket
        (n := (2 : WithTop ℕ∞)) (by simp) hXi hU hW
      simp only [nestedEval, Pi.add_apply, Pi.neg_apply]
      rw [hJacobi]
      abel

/-- Multiply every coefficient by one integer. -/
def scaleCombination {k : ℕ} (n : ℤ) (c : WordCombination k) : WordCombination k :=
  c.map fun z => (n * z.1, z.2)

/-- Scaling a combination scales its vector-field value. -/
theorem combinationEval_scale {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E) (n : ℤ) (c : WordCombination k) :
    combinationEval X (scaleCombination n c) = (n : ℝ) • combinationEval X c := by
  induction c with
  | nil => simp [scaleCombination, combinationEval]
  | cons head c ih =>
      rcases head with ⟨m, w⟩
      funext x
      change ((n * m : ℤ) : ℝ) • nestedEval X w x +
          combinationEval X (scaleCombination n c) x =
        (n : ℝ) • ((m : ℝ) • nestedEval X w x + combinationEval X c x)
      rw [ih]
      simp only [Int.cast_mul, smul_add, smul_smul, Pi.smul_apply]

/-- Multiplying coefficients leaves every word shape unchanged. -/
theorem scaleCombination_length {k : ℕ} (a : ℤ) (c : WordCombination k)
    (m : ℕ) (hm : ∀ z ∈ c, nestedLength z.2 = m) :
    ∀ z ∈ scaleCombination a c, nestedLength z.2 = m := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨p, hp, hpz⟩
  rcases p with ⟨n, w⟩
  cases hpz
  exact hm (n, w) hp

/-- Bracket a fixed standard word with every term of a
combination, retaining integer coefficients. -/
def bracketWordExpansion {k : ℕ} (u : NestedWord k) : WordCombination k → WordCombination k
  | [] => []
  | (n, w) :: c =>
      scaleCombination n (bracketExpansion u w) ++ bracketWordExpansion u c

/-- The bracket expansion of one standard word evaluates to its
bracket with the entire combination. -/
theorem bracketWordExpansion_eval {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : NestedWord k) (c : WordCombination k) :
    combinationEval X (bracketWordExpansion u c) =
      VectorField.lieBracket ℝ (nestedEval X u) (combinationEval X c) := by
  induction c with
  | nil =>
      funext x
      simp [bracketWordExpansion, combinationEval, VectorField.lieBracket]
  | cons head c ih =>
      rcases head with ⟨n, w⟩
      funext x
      simp only [bracketWordExpansion, combinationEval_append, combinationEval_scale, ih]
      rw [bracketExpansion_eval X hX u w]
      have hw : DifferentiableAt ℝ (nestedEval X w) x :=
        (nestedEval_contDiff X hX w).differentiable (by simp) x
      have hc : DifferentiableAt ℝ (combinationEval X c) x :=
        (combinationEval_contDiff X hX c).differentiable (by simp) x
      have hscaled : DifferentiableAt ℝ (fun y => (n : ℝ) • nestedEval X w y) x :=
        hw.const_smul (n : ℝ)
      change ((n : ℝ) • VectorField.lieBracket ℝ (nestedEval X u) (nestedEval X w) +
          VectorField.lieBracket ℝ (nestedEval X u) (combinationEval X c)) x =
        VectorField.lieBracket ℝ (nestedEval X u)
          ((fun y => (n : ℝ) • nestedEval X w y) + combinationEval X c) x
      rw [VectorField.lieBracket_add_right hscaled hc]
      have hsmul : VectorField.lieBracket ℝ (nestedEval X u)
          (fun y => (n : ℝ) • nestedEval X w y) x =
          (n : ℝ) • VectorField.lieBracket ℝ (nestedEval X u) (nestedEval X w) x := by
        change VectorField.lieBracket ℝ (nestedEval X u)
          ((n : ℝ) • nestedEval X w) x = _
        exact VectorField.lieBracket_const_smul_right (V := nestedEval X u)
          (W := nestedEval X w) (c := (n : ℝ)) hw
      rw [hsmul]
      simp only [Pi.add_apply, Pi.smul_apply]

/-- Bracket two combinations by bilinearity. -/
def bracketCombination {k : ℕ} (c d : WordCombination k) : WordCombination k :=
  match c with
  | [] => []
  | (n, u) :: c =>
      scaleCombination n (bracketWordExpansion u d) ++ bracketCombination c d

/-- Every term produced by bracketing a fixed standard word
has the sum of its two ordinary lengths. -/
theorem bracketWordExpansion_length {k : ℕ} (u : NestedWord k) (c : WordCombination k)
    (n : ℕ) (hn : ∀ z ∈ c, nestedLength z.2 = n) :
    ∀ z ∈ bracketWordExpansion u c, nestedLength z.2 = nestedLength u + n := by
  induction c with
  | nil => intro z hz; simp [bracketWordExpansion] at hz
  | cons head c ih =>
      rcases head with ⟨m, w⟩
      intro z hz
      have hz' : z ∈ scaleCombination m (bracketExpansion u w) ∨
          z ∈ bracketWordExpansion u c := by
        simpa [bracketWordExpansion, List.mem_append] using hz
      rcases hz' with hleft | hright
      · have hw := hn (m, w) (by simp)
        have hlength : ∀ y ∈ bracketExpansion u w,
            nestedLength y.2 = nestedLength u + n := by
          intro y hy
          have hb := bracketExpansion_length u w y hy
          rw [hw] at hb
          exact hb
        exact scaleCombination_length m (bracketExpansion u w)
          (nestedLength u + n) hlength z hleft
      · exact ih (fun y hy => hn y (by simp [hy])) z hright

/-- Bilinearity preserves the summed length for brackets of
combinations whose terms have fixed lengths. -/
theorem bracketCombination_length {k : ℕ} (c d : WordCombination k)
    (m n : ℕ) (hm : ∀ z ∈ c, nestedLength z.2 = m)
    (hn : ∀ z ∈ d, nestedLength z.2 = n) :
    ∀ z ∈ bracketCombination c d, nestedLength z.2 = m + n := by
  induction c with
  | nil => intro z hz; simp [bracketCombination] at hz
  | cons head c ih =>
      rcases head with ⟨a, u⟩
      intro z hz
      have hz' : z ∈ scaleCombination a (bracketWordExpansion u d) ∨
          z ∈ bracketCombination c d := by
        simpa [bracketCombination, List.mem_append] using hz
      rcases hz' with hleft | hright
      · have hu := hm (a, u) (by simp)
        have hword : ∀ y ∈ bracketWordExpansion u d, nestedLength y.2 = m + n := by
          intro y hy
          have hlen := bracketWordExpansion_length u d n hn y hy
          rw [hu] at hlen
          exact hlen
        exact scaleCombination_length a (bracketWordExpansion u d) (m + n)
          hword z hleft
      · exact ih (fun y hy => hm y (by simp [hy])) z hright

/-- Bracketing two combinations evaluates to the bracket of
their values. -/
theorem bracketCombination_eval {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (c d : WordCombination k) :
    combinationEval X (bracketCombination c d) =
      VectorField.lieBracket ℝ (combinationEval X c) (combinationEval X d) := by
  induction c with
  | nil =>
      funext x
      simp [bracketCombination, combinationEval, VectorField.lieBracket]
  | cons head c ih =>
      rcases head with ⟨n, u⟩
      funext x
      simp only [bracketCombination, combinationEval_append, combinationEval_scale, ih]
      rw [bracketWordExpansion_eval X hX u d]
      have hu : DifferentiableAt ℝ (nestedEval X u) x :=
        (nestedEval_contDiff X hX u).differentiable (by simp) x
      have hc : DifferentiableAt ℝ (combinationEval X c) x :=
        (combinationEval_contDiff X hX c).differentiable (by simp) x
      have hscaled : DifferentiableAt ℝ (fun y => (n : ℝ) • nestedEval X u y) x :=
        hu.const_smul (n : ℝ)
      change ((n : ℝ) • VectorField.lieBracket ℝ
          (nestedEval X u) (combinationEval X d) +
          VectorField.lieBracket ℝ (combinationEval X c) (combinationEval X d)) x =
        VectorField.lieBracket ℝ
          ((fun y => (n : ℝ) • nestedEval X u y) + combinationEval X c)
          (combinationEval X d) x
      rw [VectorField.lieBracket_add_left hscaled hc]
      have hsmul : VectorField.lieBracket ℝ
          (fun y => (n : ℝ) • nestedEval X u y) (combinationEval X d) x =
          (n : ℝ) • VectorField.lieBracket ℝ
            (nestedEval X u) (combinationEval X d) x := by
        change VectorField.lieBracket ℝ
          ((n : ℝ) • nestedEval X u) (combinationEval X d) x = _
        exact VectorField.lieBracket_const_smul_left
          (V := nestedEval X u) (W := combinationEval X d) (c := (n : ℝ)) hu
      rw [hsmul]
      simp only [Pi.add_apply, Pi.smul_apply]

/-- A binary Lie word is reduced recursively to right-nested words. -/
def binaryExpansion {k : ℕ} : Hormander.Interface.LieWord k → WordCombination k
  | .generator i => [(1, .generator i)]
  | .bracket p q => bracketCombination (binaryExpansion p) (binaryExpansion q)

/-- The recursive expansion preserves the exact ordinary leaf
count, with the drift counted once per occurrence. -/
theorem binaryExpansion_length {k : ℕ} (w : Hormander.Interface.LieWord k) :
    ∀ z ∈ binaryExpansion w, nestedLength z.2 = Hormander.lieWordLength w := by
  induction w with
  | generator i =>
      intro z hz
      simp only [binaryExpansion, List.mem_singleton] at hz
      cases hz
      simp [nestedLength, Hormander.lieWordLength]
  | bracket p q ihp ihq =>
      intro z hz
      have hp := ihp
      have hq := ihq
      have h := bracketCombination_length (binaryExpansion p) (binaryExpansion q)
        (Hormander.lieWordLength p) (Hormander.lieWordLength q) hp hq z hz
      simpa [Hormander.lieWordLength] using h

/-- Evaluation of the finite expansion agrees with Mathlib's
binary Lie-word evaluation. -/
theorem binaryExpansion_eval {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : Fin (k + 1) → E → E)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (w : Hormander.Interface.LieWord k) :
    combinationEval X (binaryExpansion w) = Hormander.lieWordEval X w := by
  induction w with
  | generator i =>
      funext x
      simp [binaryExpansion, combinationEval, nestedEval, Hormander.lieWordEval]
  | bracket p q ihp ihq =>
      simp only [binaryExpansion, Hormander.lieWordEval]
      rw [bracketCombination_eval X hX, ihp, ihq]

/-- The binary normalization identity holds on an open set for fields
that are smooth there. A local plateau cutoff gives globally smooth fields, and transfers
both recursive evaluations back to the original fields on the plateau. -/
theorem binaryExpansion_eqOn {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Ω : Set E} (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → E → E)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (w : Hormander.Interface.LieWord k) :
    EqOn (combinationEval X (binaryExpansion w)) (Hormander.lieWordEval X w) Ω := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  let S : Set E := Metric.ball x (r / 2)
  let T : Set E := Metric.closedBall x (r / 4)
  let W : Set E := Metric.ball x (r / 4)
  have hS : IsOpen S := by simp [S]
  have hT : IsClosed T := by simpa [T] using Metric.isClosed_closedBall
  have hTS : T ⊆ S := by
    dsimp [T, S]
    exact Metric.closedBall_subset_ball (by linarith)
  obtain ⟨φ, hφ, _, hsupport, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hS hT hTS
  have hφΩ : tsupport φ ⊆ Ω := by
    change closure (support φ) ⊆ Ω
    rw [hsupport]
    calc
      closure S ⊆ Metric.closedBall x (r / 2) := by
        dsimp [S]
        exact Metric.closure_ball_subset_closedBall
      _ ⊆ Metric.ball x r := by
        exact Metric.closedBall_subset_ball (by linarith)
      _ ⊆ Ω := hball
  have hW : IsOpen W := by simp [W]
  have hWsubT : W ⊆ T := by
    dsimp [W, T]
    exact Metric.ball_subset_closedBall
  have hxW : x ∈ W := by
    dsimp [W]
    rw [Metric.mem_ball]
    simp
    linarith
  let Y : Fin (k + 1) → E → E := fun i y => φ y • X i y
  have hY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i) := by
    intro i
    exact localized_smul_smooth hΩ φ hφ hφΩ (X i) (hX i)
  have hXY : ∀ i, EqOn (X i) (Y i) W := by
    intro i y hy
    have hyT : y ∈ T := hWsubT hy
    have hφy : φ y = 1 := (hone y).mp hyT
    simp [Y, hφy]
  have hComb := combinationEval_eqOn_of_eqOn hW X Y hXY (binaryExpansion w) hxW
  have hWord := Hormander.F.lieWordEval_eqOn_of_eqOn hW X Y hXY w hxW
  have hGlobal := binaryExpansion_eval Y hY w
  calc
    combinationEval X (binaryExpansion w) x = combinationEval Y (binaryExpansion w) x := hComb
    _ = Hormander.lieWordEval Y w x := congrFun hGlobal x
    _ = Hormander.lieWordEval X w x := hWord.symm

end Hormander.C

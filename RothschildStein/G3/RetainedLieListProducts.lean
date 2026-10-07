-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLieListJets
public import RothschildStein.G3.QuasiExponentialLog
@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem retainedLieProduct_neg_reverse {a s : ℕ} {p : Fin a → ℕ+}
    (f g : formalSpan a s p) : retainedLieProduct (-g) (-f) = -(retainedLieProduct f g) := by
  have hz : retainedLieProduct (retainedLieProduct f g) (retainedLieProduct (-g) (-f)) = 0 := by
    rw [retainedLieProduct_assoc,← retainedLieProduct_assoc g (-g) (-f),retainedLieProduct_neg_right,
      retainedLieProduct_zero_left,retainedLieProduct_neg_right]
  calc
    _ = retainedLieProduct (retainedLieProduct (-(retainedLieProduct f g)) (retainedLieProduct f g))
        (retainedLieProduct (-g) (-f)) := by rw [retainedLieProduct_neg_left,retainedLieProduct_zero_left]
    _ = retainedLieProduct (-(retainedLieProduct f g))
        (retainedLieProduct (retainedLieProduct f g) (retainedLieProduct (-g) (-f))) := retainedLieProduct_assoc _ _ _
    _ = _ := by rw [hz,retainedLieProduct_zero_right]

theorem retainedLieListProduct_append {a s : ℕ} {p : Fin a → ℕ+}
    (fs gs : List (formalSpan a s p)) :
    retainedLieListProduct (fs++gs) = retainedLieProduct (retainedLieListProduct fs) (retainedLieListProduct gs) := by
  induction fs with
  | nil => simp only [retainedLieListProduct,List.nil_append,List.foldr_nil,retainedLieProduct_zero_left]
  | cons f fs ih =>
    change retainedLieProduct f (retainedLieListProduct (fs++gs)) =
      retainedLieProduct (retainedLieProduct f (retainedLieListProduct fs)) (retainedLieListProduct gs)
    rw [ih,retainedLieProduct_assoc]

theorem retainedLieListProduct_inverse {a s : ℕ} {p : Fin a → ℕ+}
    (fs : List (formalSpan a s p)) :
    retainedLieListProduct (fs.reverse.map fun f => -f) = -(retainedLieListProduct fs) := by
  induction fs with
  | nil => simp [retainedLieListProduct]
  | cons f fs ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    rw [retainedLieListProduct_append,ih]
    simp only [retainedLieListProduct,List.foldr_cons,List.foldr_nil,retainedLieProduct_zero_right]
    exact retainedLieProduct_neg_reverse f (retainedLieListProduct fs)

def primitiveScheduleLieInput {a s : ℕ} {p : Fin a → ℕ+}
    (b : Fin a × Bool) : formalSpan a s p :=
  if b.2 then wordLieElement [b.1] else -(wordLieElement [b.1])

theorem primitiveScheduleLieInput_flip {a s : ℕ} {p : Fin a → ℕ+}
    (b : Fin a × Bool) : primitiveScheduleLieInput (s := s) (p := p) (b.1,!b.2) =
      -(primitiveScheduleLieInput b) := by
  rcases b with ⟨i,b⟩
  cases b <;> simp [primitiveScheduleLieInput]

theorem primitiveScheduleLieInput_inverse {a s : ℕ} {p : Fin a → ℕ+}
    (S : List (Fin a × Bool)) :
    (G1.inverseSchedule S).map (primitiveScheduleLieInput (s := s) (p := p)) =
      (S.map primitiveScheduleLieInput).reverse.map (fun f => -f) := by
  simp only [G1.inverseSchedule,List.map_map,List.map_reverse]
  congr 1
  apply List.map_congr_left
  intro b _
  exact primitiveScheduleLieInput_flip b

theorem commutatorSchedule_retainedLieListProduct {a s : ℕ} {p : Fin a → ℕ+}
    (I : List (Fin a)) :
    retainedLieListProduct ((G1.commutatorSchedule I).map (primitiveScheduleLieInput (s := s) (p := p))) =
      quasiExponentialLog I := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    cases I with
    | nil => simp [G1.commutatorSchedule,retainedLieListProduct,primitiveScheduleLieInput,quasiExponentialLog]
    | cons j I =>
      simp only [G1.commutatorSchedule,List.map_append]
      rw [retainedLieListProduct_append,retainedLieListProduct_append,
        retainedLieListProduct_append,primitiveScheduleLieInput_inverse,retainedLieListProduct_inverse]
      simp only [List.map_cons,List.map_nil,retainedLieListProduct,List.foldr_cons,List.foldr_nil,
        primitiveScheduleLieInput,ite_true,retainedLieProduct_zero_right] at *
      rw [ih]
      rfl
end RothschildStein.G3

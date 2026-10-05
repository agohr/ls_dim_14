import QuaternionicSymmetry.CompactSymplecticStabilizerBlocks

/-! Reindex the two complex halves so that the distinguished quaternionic
coordinate is a `Fin 2` block and its complement is the usual pair of
`Fin n` blocks. This is an honest equivalence of the matrix index types. -/

namespace QuaternionicSymmetry.CompactSymplecticStabilizerIndex

open CompactSymplecticStabilizerBlocks

/-- Coordinates of the first quaternionic line and its complement. -/
def blockIndexEquiv (n : ℕ) :
    (Fin (n + 1) ⊕ Fin (n + 1)) ≃ (Fin 2 ⊕ (Fin n ⊕ Fin n)) where
  toFun
    | Sum.inl i => Fin.cases (Sum.inl (0 : Fin 2))
        (fun j => Sum.inr (Sum.inl j)) i
    | Sum.inr i => Fin.cases (Sum.inl (1 : Fin 2))
        (fun j => Sum.inr (Sum.inr j)) i
  invFun
    | Sum.inl i => Fin.cases (Sum.inl (0 : Fin (n + 1)))
        (fun _ => Sum.inr (0 : Fin (n + 1))) i
    | Sum.inr (Sum.inl j) => Sum.inl j.succ
    | Sum.inr (Sum.inr j) => Sum.inr j.succ
  left_inv := by
    intro i
    cases i with
    | inl j =>
      refine Fin.cases ?_ (fun k => ?_) j <;> simp
    | inr j =>
      refine Fin.cases ?_ (fun k => ?_) j
      · change (Fin.cases (Sum.inl (0 : Fin (n + 1)))
          (fun _ => Sum.inr (0 : Fin (n + 1)))
          ((0 : Fin 1).succ)) = Sum.inr 0
        exact Fin.cases_succ _
      · simp
  right_inv := by
    intro i
    rcases i with i | i
    · fin_cases i <;> rfl
    · rcases i with j | j <;> simp

theorem blockIndexEquiv_firstPair_iff (n : ℕ)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) :
    InFirstPair n i ↔ ∃ j : Fin 2, blockIndexEquiv n i = Sum.inl j := by
  rcases i with i | i
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp [InFirstPair, blockIndexEquiv]
    · simp [InFirstPair, blockIndexEquiv]
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp [InFirstPair, blockIndexEquiv]
    · simp [InFirstPair, blockIndexEquiv]

end QuaternionicSymmetry.CompactSymplecticStabilizerIndex

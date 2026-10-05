import QuaternionicSymmetry.Arithmetic

/-!
The finite dimension induction used by the symmetry argument. `Object` is
intended to be the eventual type of compact positive quaternionic-Kähler
manifolds and `Component M N` the actual positive-dimensional quaternionic
fixed-component construction. This module is only the well-founded logical
step; it makes no claim that those geometric objects or recognition inputs
have been constructed.
-/

namespace QuaternionicSymmetry.FiniteDimensionInduction

/-- Recognition through a finite bound from the classical positive dimensions
and a geometric step using recognition only for proper fixed components. -/
theorem through_bound
    {Object : Type*} (limit : ℕ) (dim : Object → ℕ)
    (Recognised : Object → Prop) (Component : Object → Object → Prop)
    (classical : ∀ M, 0 < dim M → dim M ≤ 4 → Recognised M)
    (geometricStep : ∀ M, 5 ≤ dim M → dim M ≤ limit →
      (∀ N, Component M N → 0 < dim N → dim N < dim M → Recognised N) →
      Recognised M) :
    ∀ M, 0 < dim M → dim M ≤ limit → Recognised M := by
  intro M hpositive hM
  have induction (k : ℕ) :
      ∀ N, dim N = k → 0 < k → k ≤ limit → Recognised N := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro N hdim hkpositive hk
      by_cases hsmall : k ≤ 4
      · exact classical N (by omega) (by omega)
      · apply geometricStep N (by omega) (by omega)
        intro C hcomponent hpositiveC hproper
        exact ih (dim C) (by omega) C rfl hpositiveC (by omega)
  exact induction (dim M) M rfl hpositive hM

/-- The finite range of the textbook's primary classification argument. -/
theorem through_twelve
    {Object : Type*} (dim : Object → ℕ) (Recognised : Object → Prop)
    (Component : Object → Object → Prop)
    (classical : ∀ M, 0 < dim M → dim M ≤ 4 → Recognised M)
    (geometricStep : ∀ M, 5 ≤ dim M → dim M ≤ 12 →
      (∀ N, Component M N → 0 < dim N → dim N < dim M → Recognised N) →
      Recognised M) :
    ∀ M, 0 < dim M → dim M ≤ 12 → Recognised M :=
  through_bound 12 dim Recognised Component classical geometricStep

/-- Final finite contradiction, conditional on the two geometric outputs.
`smallSymmetry` is the minimal-counterexample symmetry theorem after proper
components have been recognised; `indexLower` is characteristic positivity
compared with the virtual index. Neither is asserted for arbitrary objects. -/
theorem through_bound_of_symmetry_and_index
    {Object : Type*} (limit : ℕ) (dim isoDim : Object → ℕ)
    (Recognised : Object → Prop) (Component : Object → Object → Prop)
    (classical : ∀ M, 0 < dim M → dim M ≤ 4 → Recognised M)
    (smallSymmetry : ∀ M, 5 ≤ dim M → dim M ≤ limit →
      (∀ N, Component M N → 0 < dim N → dim N < dim M → Recognised N) →
      ¬ Recognised M → isoDim M ≤ 3)
    (indexLower : ∀ M, 5 ≤ dim M → dim M ≤ limit →
      delta (dim M) + 1 ≤ isoDim M) :
    ∀ M, 0 < dim M → dim M ≤ limit → Recognised M := by
  apply through_bound limit dim Recognised Component classical
  intro M hfive hlimit hcomponents
  by_contra hnot
  have hsmall := smallSymmetry M hfive hlimit hcomponents hnot
  have hlarge := indexLower M hfive hlimit
  have hdelta : 6 ≤ delta (dim M) := by
    unfold delta
    split_ifs <;> omega
  omega

/-- The primary range once the geometric and index deductions are supplied.
Those deductions include internal bridges as well as cited inputs. -/
theorem through_twelve_of_symmetry_and_index
    {Object : Type*} (dim isoDim : Object → ℕ)
    (Recognised : Object → Prop) (Component : Object → Object → Prop)
    (classical : ∀ M, 0 < dim M → dim M ≤ 4 → Recognised M)
    (smallSymmetry : ∀ M, 5 ≤ dim M → dim M ≤ 12 →
      (∀ N, Component M N → 0 < dim N → dim N < dim M → Recognised N) →
      ¬ Recognised M → isoDim M ≤ 3)
    (indexLower : ∀ M, 5 ≤ dim M → dim M ≤ 12 →
      delta (dim M) + 1 ≤ isoDim M) :
    ∀ M, 0 < dim M → dim M ≤ 12 → Recognised M :=
  through_bound_of_symmetry_and_index 12 dim isoDim Recognised Component
    classical smallSymmetry indexLower

/-- The same induction endpoint through dimension fourteen, conditional on
its extra H2 reserve positivity in the index lower-bound premise. -/
theorem through_fourteen_of_symmetry_and_index
    {Object : Type*} (dim isoDim : Object → ℕ)
    (Recognised : Object → Prop) (Component : Object → Object → Prop)
    (classical : ∀ M, 0 < dim M → dim M ≤ 4 → Recognised M)
    (smallSymmetry : ∀ M, 5 ≤ dim M → dim M ≤ 14 →
      (∀ N, Component M N → 0 < dim N → dim N < dim M → Recognised N) →
      ¬ Recognised M → isoDim M ≤ 3)
    (indexLower : ∀ M, 5 ≤ dim M → dim M ≤ 14 →
      delta (dim M) + 1 ≤ isoDim M) :
    ∀ M, 0 < dim M → dim M ≤ 14 → Recognised M :=
  through_bound_of_symmetry_and_index 14 dim isoDim Recognised Component
    classical smallSymmetry indexLower

end QuaternionicSymmetry.FiniteDimensionInduction

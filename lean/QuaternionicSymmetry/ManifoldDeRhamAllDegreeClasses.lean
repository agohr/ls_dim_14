import QuaternionicSymmetry.ManifoldDeRhamAllDegrees

/-!
The homogeneous form-to-class map, with the ordinary closed-form
representative in degree zero and the closed/exact quotient above degree zero.
-/

namespace QuaternionicSymmetry.ManifoldDeRhamAllDegreeClasses

open QuaternionicSymmetry.ManifoldDifferentialForms
  QuaternionicSymmetry.ManifoldDeRhamWedge
  QuaternionicSymmetry.ManifoldDeRhamRing
  QuaternionicSymmetry.ManifoldDeRhamAllDegrees
  QuaternionicSymmetry.ManifoldDeRhamDegreeZero
open scoped Manifold ContDiff Topology

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The canonical map from a closed form of any degree to its de Rham class. -/
noncomputable def classOfDegree : (n : ℕ) →
    closedForms (E := E) (M₀ := M) n →
    CohomologyByDegree (E := E) (M := M) n
  | 0, α => α
  | _ + 1, α => QuotientAddGroup.mk α

theorem classOfDegree_zero
    (a : closedForms (E := E) (M₀ := M) 0) :
    classOfDegree 0 a = a := rfl

theorem classOfDegree_positive (k : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1)) :
    classOfDegree (k + 1) α = QuotientAddGroup.mk α := rfl

theorem zeroPositive_class_mul (l : ℕ)
    (a : closedForms (E := E) (M₀ := M) 0)
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    zeroPositiveWedge l (classOfDegree 0 a)
      (classOfDegree (l + 1) β) =
      classOfDegree (l + 1) (zeroPositiveClosed l a β) := by
  rfl

theorem positiveZero_class_mul (k : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (a : closedForms (E := E) (M₀ := M) 0) :
    positiveZeroWedge k (classOfDegree (k + 1) α)
      (classOfDegree 0 a) =
      classOfDegree (k + 1) (positiveZeroClosed k α a) := by
  rfl

theorem zeroZero_class_mul
    (a b : closedForms (E := E) (M₀ := M) 0) :
    zeroZeroWedge (classOfDegree 0 a) (classOfDegree 0 b) =
      classOfDegree 0 (closedWedgeAll a b) := rfl

theorem classOfDegree_one :
    classOfDegree (E := E) (M := M) 0 (oneClass (E := E) (M := M)) =
      unitDegree (E := E) (M := M) := rfl

/-- Right multiplication by the homogeneous degree-zero unit. -/
theorem wedgeDegree_unit_right (n : ℕ)
    (a : CohomologyByDegree (E := E) (M := M) n) :
    wedgeDegree n 0 a unitDegree = a := by
  cases n with
  | zero => exact zeroZeroWedge_one_right a
  | succ k => exact positiveZeroWedge_one_right k a

end QuaternionicSymmetry.ManifoldDeRhamAllDegreeClasses

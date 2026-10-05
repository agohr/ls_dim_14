import QuaternionicSymmetry.ManifoldFormExteriorEvaluation

/-! A ring homomorphism evaluates the global graded closed-form algebra in
the even exterior algebra of any chosen chart and linear tangent frame. -/
namespace QuaternionicSymmetry.ManifoldEvenClosedEvaluation
open Module ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamRing
open ManifoldEvenClosedAlgebra ManifoldFormExteriorEvaluation
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (p : M) (y : E) (L : E →L[ℝ] E)

abbrev FiberAlgebra := EvenForms.evenSubalgebra ℝ (Module.Dual ℝ E)

def closedValue (n : ℕ) : closedForms (E := E) (M₀ := M) n →ₗ[ℝ]
    ExteriorAlgebra ℝ (Module.Dual ℝ E) :=
  (value p y L n).comp ((smoothForms (I := 𝓘(ℝ,E)) (M := M) (n := n)).subtype.comp
    (closedForms n).subtype)

theorem closedValue_cast {m n : ℕ} (h : m = n)
    (a : closedForms (E := E) (M₀ := M) (m+1)) :
    closedValue p y L (n+1) (castClosed h a) = closedValue p y L (m+1) a := by
  change value p y L _ (castClosed h a).val.val = _
  rw [castClosed_form, value_cast]
  rfl

theorem closedValue_wedge (m n : ℕ)
    (a : closedForms (E := E) (M₀ := M) (m+1))
    (b : closedForms (E := E) (M₀ := M) (n+1)) :
    closedValue p y L (m+n+1+1) (closedWedge m n a b) =
      closedValue p y L (m+1) a * closedValue p y L (n+1) b := by
  change value p y L _ (castForm _ (formWedge a.val.val b.val.val)) = _
  rw [value_cast, value_wedge]
  rfl

theorem closedValue_even (k : ℕ)
    (a : closedForms (E := E) (M₀ := M) (4*k+3+1)) :
    closedValue p y L (4*k+3+1) a ∈ EvenForms.evenSubalgebra ℝ (Module.Dual ℝ E) := by
  apply EvenForms.even_degree_le (2*k+2)
  rw [show 2*(2*k+2) = 4*k+3+1 by omega]
  exact (representative p y L (4*k+3+1) a.val.val).property

def gradeValue : (n : ℕ) → Grade E M n →ₗ[ℝ] FiberAlgebra (E := E)
  | 0 => Algebra.linearMap ℝ _
  | k+1 =>
    { toFun := fun a => ⟨closedValue p y L (4*k+3+1) a, closedValue_even p y L k a⟩
      map_add' := fun a b => Subtype.ext ((closedValue p y L _).map_add a b)
      map_smul' := fun r a => Subtype.ext ((closedValue p y L _).map_smul r a) }

theorem gradeValue_cast {m n : ℕ} (h : m = n) (a : Grade E M m) :
    gradeValue p y L n (castGrade h a) = gradeValue p y L m a := by
  cases h
  rfl

theorem gradeValue_mul (m n : ℕ) (a : Grade E M m) (b : Grade E M n) :
    gradeValue p y L (m+n) (gradeMul m n a b) =
      gradeValue p y L m a * gradeValue p y L n b := by
  cases m with
  | zero =>
      cases n with
      | zero => exact map_mul (algebraMap ℝ (FiberAlgebra (E := E))) a b
      | succ k =>
          change ℝ at a
          change PositiveClosed (E := E) (M := M) (4*k+3) at b
          change gradeValue p y L _ (castGrade (Nat.zero_add (k+1)).symm (a • b)) = _
          rw [gradeValue_cast, map_smul]
          exact Algebra.smul_def _ _
  | succ k =>
      cases n with
      | zero =>
          change ℝ at b
          change gradeValue p y L (k+1) (b • a) = _
          rw [map_smul]
          rw [Algebra.smul_def, mul_comm]
          rfl
      | succ l =>
          apply Subtype.ext
          change closedValue p y L _ (castClosed _ (closedWedge _ _ a b)) = _
          rw [closedValue_cast, closedValue_wedge]
          rfl

def evaluate : Total (E := E) (M := M) →+* FiberAlgebra (E := E) :=
  DirectSum.toSemiring (fun n => (gradeValue p y L n).toAddMonoidHom)
    (by change algebraMap ℝ (FiberAlgebra (E := E)) 1 = 1; exact map_one _)
    (fun a b => gradeValue_mul p y L _ _ a b)

theorem evaluate_of (n : ℕ) (a : Grade E M n) :
    evaluate p y L (DirectSum.of (Grade E M) n a) = gradeValue p y L n a :=
  DirectSum.toSemiring_of _ _ _ n a

end
end QuaternionicSymmetry.ManifoldEvenClosedEvaluation

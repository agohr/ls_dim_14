import QuaternionicSymmetry.ManifoldEvenClosedAlgebra
import QuaternionicSymmetry.ManifoldEvenCharacteristicAlgebra

/-! Taking the de Rham class of genuine closed forms preserves the graded
ring structure, including constant degree-zero coefficients. -/
namespace QuaternionicSymmetry.ManifoldEvenClosedClassMap
open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamRing
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def classGrade (n : ℕ) :
    ManifoldEvenClosedAlgebra.Grade E M n →ₗ[ℝ]
      ManifoldEvenCharacteristicAlgebra.Grade E M n := by
  cases n with
  | zero => exact LinearMap.id
  | succ k =>
      exact { toFun := closedFormClass (4 * k + 3)
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }

theorem classGrade_cast {p q : ℕ} (h : p = q)
    (a : ManifoldEvenClosedAlgebra.Grade E M p) :
    classGrade q (ManifoldEvenClosedAlgebra.castGrade h a) =
      ManifoldEvenCharacteristicAlgebra.castGrade h (classGrade p a) := by
  cases h
  rfl

theorem classGrade_mul (p q : ℕ)
    (a : ManifoldEvenClosedAlgebra.Grade E M p)
    (b : ManifoldEvenClosedAlgebra.Grade E M q) :
    classGrade (p + q) (ManifoldEvenClosedAlgebra.gradeMul p q a b) =
      ManifoldEvenCharacteristicAlgebra.gradeMul p q (classGrade p a) (classGrade q b) := by
  cases p with
  | zero =>
      cases q with
      | zero => rfl
      | succ l =>
          change ℝ at a
          change ManifoldEvenClosedAlgebra.PositiveClosed (E := E) (M := M) (4*l+3) at b
          change classGrade _ (ManifoldEvenClosedAlgebra.castGrade
            (Nat.zero_add (l+1)).symm (a • b)) = _
          rw [classGrade_cast, map_smul]
          rfl
  | succ k =>
      cases q with
      | zero => exact (classGrade (k+1)).map_smul b a
      | succ l =>
          change closedFormClass _ (castClosed _ (closedWedge _ _ a b)) =
            castClass _ (cohomologyWedge _ _ (closedFormClass _ a) (closedFormClass _ b))
          rw [← closedFormClass_wedge]
          exact (castClass_mk _ _).symm

def classToTotal (n : ℕ) :
    ManifoldEvenClosedAlgebra.Grade E M n →+
      ManifoldEvenCharacteristicAlgebra.Total (E := E) (M := M) :=
  (DirectSum.of (ManifoldEvenCharacteristicAlgebra.Grade E M) n).comp
    (classGrade n).toAddMonoidHom

theorem classToTotal_mul {p q : ℕ}
    (a : ManifoldEvenClosedAlgebra.Grade E M p)
    (b : ManifoldEvenClosedAlgebra.Grade E M q) :
    classToTotal (p+q) (ManifoldEvenClosedAlgebra.gradeMul p q a b) =
      classToTotal p a * classToTotal q b := by
  simp only [classToTotal, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    classGrade_mul]
  exact (DirectSum.of_mul_of _ _).symm

def classMap : ManifoldEvenClosedAlgebra.Total (E := E) (M := M) →+*
    ManifoldEvenCharacteristicAlgebra.Total (E := E) (M := M) :=
  DirectSum.toSemiring classToTotal rfl classToTotal_mul

theorem classMap_of (n : ℕ) (a : ManifoldEvenClosedAlgebra.Grade E M n) :
    classMap (DirectSum.of (ManifoldEvenClosedAlgebra.Grade E M) n a) =
      DirectSum.of (ManifoldEvenCharacteristicAlgebra.Grade E M) n (classGrade n a) :=
  DirectSum.toSemiring_of _ _ _ n a

end
end QuaternionicSymmetry.ManifoldEvenClosedClassMap

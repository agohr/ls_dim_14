import QuaternionicSymmetry.QuaternionicClosedSourceGenerators
import QuaternionicSymmetry.QuaternionicManifoldCorrectedTransgression
import QuaternionicSymmetry.ManifoldClosedPolynomialComparison
import QuaternionicSymmetry.ManifoldClosedPolynomialRepresentative

/-! The normalized source generators and all their polynomial de Rham classes
are independent of the solder correction parameter. -/
namespace QuaternionicSymmetry.QuaternionicClosedSourceClassInvariance
open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamRing
open ManifoldDeRhamAllDegrees ManifoldEvenClosedClassMap
open QuaternionicClosedSourceGenerators QuaternionicCorrectedSourceTraceForms
open QuaternionicManifoldCorrectedTracePowers QuaternionicManifoldCorrectedTransgression
open LocalChernWeilTracePowers LocalChernWeilOrderedTransgression
open ManifoldClosedPolynomialComparison
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem class_cast_transfer {d a b : ℕ} (ha : d = a+1) (hb : d = b+1)
    (α β : closedForms (E := E) (M₀ := M) d)
    (h : closedFormClass a (castClosedDegree ha α) =
      closedFormClass a (castClosedDegree ha β)) :
    closedFormClass b (castClosedDegree hb α) =
      closedFormClass b (castClosedDegree hb β) := by
  have hab : a = b := by omega
  subst b
  exact h

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem castClosedDegree_smul {a b : ℕ} (h : a = b) (c : ℝ)
    (α : closedForms (E := E) (M₀ := M) a) :
    castClosedDegree h (c • α) = c • castClosedDegree h α := by
  cases h
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem castClosedDegree_eq {a b : ℕ} (h : a = b)
    (α : closedForms (E := E) (M₀ := M) a) : castClosedDegree h α = h ▸ α := by
  cases h
  rfl

theorem sourceGrade_class_eq (s t : ℝ) (k : ℕ) :
    classGrade (k+1) (sourceGrade S Q D t k) =
      classGrade (k+1) (sourceGrade S Q D s k) := by
  have h := closedTracePower_class_eq S Q D s t (2*(k+1)-1)
  have h' : closedFormClass (primitiveDegree (2*(k+1)-1))
      (castClosedDegree (primitiveDegree_add_one _).symm
        (closedTracePower S Q D t (2*(k+1)-1))) =
    closedFormClass (primitiveDegree (2*(k+1)-1))
      (castClosedDegree (primitiveDegree_add_one _).symm
        (closedTracePower S Q D s (2*(k+1)-1))) := by
    simpa only [castClosedDegree_eq, closedFormClass] using h
  have ht := class_cast_transfer _ (sourceDegree k) _ _ h'
  change closedFormClass _ (castClosedDegree _ (_ • _)) =
    closedFormClass _ (castClosedDegree _ (_ • _))
  rw [castClosedDegree_smul, castClosedDegree_smul,
    closedFormClass_smul, closedFormClass_smul, ht]

theorem classGenerators_eq (s t : ℝ) :
    classGenerators (generators S Q D t) = classGenerators (generators S Q D s) := by
  unfold classGenerators generators
  congr 1 <;> apply sourceGrade_class_eq

theorem polynomial_class_eq (s t : ℝ) (P : DimensionThirteenFourteenDensity.P) :
    classMap (ManifoldSevenVariableClosedEvaluation.evaluate (generators S Q D t) P) =
      classMap (ManifoldSevenVariableClosedEvaluation.evaluate (generators S Q D s) P) := by
  rw [class_evaluate, class_evaluate, classGenerators_eq S Q D s t]

theorem representative_class_eq (s t : ℝ) {n : ℕ}
    (P : DimensionThirteenFourteenDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous
      ManifoldSevenVariableClosedEvaluation.slotGrade P n) :
    classGrade n (ManifoldClosedPolynomialRepresentative.closedRepresentative
      (generators S Q D t) P hP) =
    classGrade n (ManifoldClosedPolynomialRepresentative.closedRepresentative
      (generators S Q D s) P hP) := by
  apply DirectSum.of_injective
  rw [← ManifoldClosedPolynomialRepresentative.class_evaluate_eq_of,
    ← ManifoldClosedPolynomialRepresentative.class_evaluate_eq_of,
    classGenerators_eq S Q D s t]

end
end QuaternionicSymmetry.QuaternionicClosedSourceClassInvariance

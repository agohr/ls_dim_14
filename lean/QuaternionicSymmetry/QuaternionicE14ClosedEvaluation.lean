import QuaternionicSymmetry.QuaternionicClosedSourceEvaluation
import QuaternionicSymmetry.ManifoldClosedPolynomialRepresentative
import QuaternionicSymmetry.QuaternionicE14OrbitalSums
import QuaternionicSymmetry.ManifoldE14OrbitalWeights

/-! All seven actual closed source generators realize the E14 orbital
evaluation in the same orthonormal tangent frame and Weyl coefficients. -/
namespace QuaternionicSymmetry.QuaternionicE14ClosedEvaluation
open Module QuaternionicClosedSourceGenerators QuaternionicClosedSourceEvaluation
open ManifoldClosedPolynomialComparison ManifoldSevenVariableClosedEvaluation
open ManifoldEvenClosedEvaluation QuaternionicE14OrbitalPointwise
open QuaternionicWeylMatrixCoefficients QuaternionicCurvatureFiniteExpansion
open QuaternionicCurvatureOrbitalSign ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarInput QuaternionicTracePositivity
open ManifoldClosedPolynomialRepresentative
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

set_option maxRecDepth 2000 in
theorem seven_generator_values
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (b : Basis ι ℝ E) (t : ℝ)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ∃ (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
      (hW : HyperWeylFiber S W),
      (fun i : Fin 7 => embed (V := E)
        (fiberValues (generators S Q D t) p y
          (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap i)) =
      sevenValues S b ((t ^ 2 / Real.pi) ^ 2)
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b) := by
  obtain ⟨W, hW, htrace⟩ := sourceGrade_value S Q D hsp hdecomp b t p y hy (ht p y hy).symm
  refine ⟨W, hW, ?_⟩
  funext i
  fin_cases i <;>
    simp [fiberValues, generatorValues, generators, sevenValues,
      ManifoldEvenClosedEvaluation.evaluate_of]
  · rw [quarterGrade_value S Q D hsp (t^2) ht b p y hy]
    exact (embed (V := E)).toLinearMap.map_smul _ _
  · rw [htrace 0]; rfl
  · rw [htrace 1]; rfl
  · rw [htrace 2]; rfl
  · rw [htrace 3]; rfl
  · rw [htrace 4]; rfl
  · rw [htrace 5]; rfl

omit [Nontrivial E] [Fintype ι] in
theorem pointwise_representative_complex
    (g : Generators (E := E) (M := M)) {n : ℕ}
    (P : DimensionThirteenFourteenDensity.P)
    (hP : MvPolynomial.IsWeightedHomogeneous slotGrade P n)
    (p : M) (y : E) (L : E →L[ℝ] E) :
    embed (V := E) (gradeValue p y L n (closedRepresentative g P hP)) =
      MvPolynomial.aeval (fun i => embed (V := E) (fiberValues g p y L i)) P := by
  rw [pointwise_representative]
  exact MvPolynomial.comp_aeval_apply _ ((embed (V := E)).restrictScalars ℚ) P

end
end QuaternionicSymmetry.QuaternionicE14ClosedEvaluation

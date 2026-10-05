import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
import QuaternionicSymmetry.QuaternionicCurvatureOrbitalSign
import QuaternionicSymmetry.QuaternionicCorrectedCurvatureMatrix

/-! The actual normalized corrected curvature has the finite Hermitian
matrix/two-form expansion, relative to the two explicitly registered KSW
formulas. Chart tangent arguments are transported by the fixed solder map;
the Weyl symmetries and coefficient forms live in the orthonormal model. -/
namespace QuaternionicSymmetry.QuaternionicManifoldWeylMatrixExpansion
open Module ManifoldQuaternionicKSWEq38Input ManifoldQuaternionicKSWScalarInput
open QuaternionicCurvatureFiniteExpansion QuaternionicCurvatureMatrixExpansion
open QuaternionicCurvatureOrbitalSign QuaternionicCorrectedCurvatureMatrix
open QuaternionicManifoldCorrectedConnection QuaternionicManifoldFixedSolder
open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardHilbertStructure
open QuaternionicOperatorMatrix QuaternionicOperatorMatrixLinear
open scoped Manifold ContDiff Quaternion Matrix
noncomputable section
variable {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance

theorem sourceMatrix_eq_of_upper (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (A : operatorSpace S)
    (h : LocalConnection.curvature (correctedConnection S Q D t p) y u v =
      upperEmbedding A.val) :
    sourceCurvatureMatrix S Q D t p y u v hy = (sourceMatrixMap S A).val := by
  change (1 / (2 * Real.pi) : ℝ) • (Complex.I •
    operatorMatrix (standardStructure S)
      (LocalConnection.curvature (correctedConnection S Q D t p) y u v).toLinearMap _) =
    (1 / (2 * Real.pi) : ℝ) • (Complex.I •
      operatorMatrix (standardStructure S) (upperEmbedding A.val).toLinearMap
        (((standardStructure S).mem_skewCentralizer_iff _).mp (upperEmbedding_mem S A)).2.1)
  congr 3
  exact congrArg ContinuousLinearMap.toLinearMap h

theorem correctedCurvature_finite_expansion [Fintype ι]
    (hsp : KSWSp1CurvatureFormula S Q D)
    (hdecomp : KSWEq38Decomposition S Q D)
    (b : Basis ι ℝ E) (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) :
    ∃ (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
      (hW : HyperWeylFiber S W),
      (∀ a : Index S, coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b a ∈
        HyperholomorphicExterior.formSpace S b) ∧
      ∀ u v : E,
        sourceCurvatureMatrix S Q D t p y u v hy =
          ∑ a : Index S,
            BilinearExterior.evaluate (fixedSolder S Q p y u) (fixedSolder S Q p y v)
              (HyperholomorphicExterior.form b
                (QuaternionicBilinearOperator.operator
                  (coefficient S W (HyperWeylFiber.mem_skewCentralizer S hW) a)).toLinearMap) •
              (sourceMatrixMap S (operatorBasis S a)).val := by
  obtain ⟨W, hW, hblock⟩ :=
    correctedCurvature_eq_hyper_block S Q D hsp hdecomp t p y hy ht
  refine ⟨W, hW, coefficientExterior_mem S W (HyperWeylFiber.mem_skewCentralizer S hW) b hW.1 hW.2.2.2.2.1, ?_⟩
  intro u v
  let A : operatorSpace S :=
    ⟨W (fixedSolder S Q p y u) (fixedSolder S Q p y v), (HyperWeylFiber.mem_skewCentralizer S hW) _ _⟩
  have heq : LocalConnection.curvature (correctedConnection S Q D t p) y u v =
      upperEmbedding A.val := by
    apply ContinuousLinearMap.ext
    intro z
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
    exact hblock u v z
  rw [sourceMatrix_eq_of_upper S Q D t p y u v hy A heq]
  have hexp := sourceMatrix_twoForm_expansion S W (HyperWeylFiber.mem_skewCentralizer S hW) b hW.1
    (fixedSolder S Q p y u) (fixedSolder S Q p y v)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, A] using
    (congrArg Subtype.val hexp).symm

end
end QuaternionicSymmetry.QuaternionicManifoldWeylMatrixExpansion

import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionLaws

/-! The KSW scalar-component formula follows from the full curvature decomposition.

The upper model term and hyper-Weyl remainder commute with the quaternionic
structure, so their scalar projections vanish. Projecting the retained KSW
Equation (3.8) contract therefore proves the Lemma 3.10 contract, with exactly
its existing normalization. No second curvature premise is needed.
The proof was first checked in contract-audit experiment E09. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWScalarFromDecomposition

open QuaternionicSymmetry
open ManifoldQuaternionicConnection ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input QuaternionicLieAlgebraProjection
open QuaternionicKSWUpperModel QuaternionicStandardSolderSquare
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [FiniteDimensional ℝ E] in
theorem commutes_synth_of_I_J (S : QuaternionicStructure E) (A : E →L[ℝ] E)
    (hI : ∀ v, A (S.I v) = S.I (A v))
    (hJ : ∀ v, A (S.J v) = S.J (A v)) (b : Fin 3 → ℝ) :
    A * synth S b = synth S b * A := by
  have hgen (i : Fin 3) :
      A * quaternionicGenerator S i = quaternionicGenerator S i * A := by
    fin_cases i
    · exact ContinuousLinearMap.ext hI
    · exact ContinuousLinearMap.ext hJ
    · apply ContinuousLinearMap.ext
      intro v
      change A (S.I (S.J v)) = S.I (S.J (A v))
      rw [hI, hJ]
  rw [ManifoldQuaternionicRankThreeOrthogonal.synth_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => b i • z) (hgen i))

theorem scalarProjection_upperSquare_zero (S : QuaternionicStructure E) (u v : E) :
    scalarProjection S (upperSquare S u v) = 0 := by
  apply scalarProjection_eq_zero_of_commutes
  exact commutes_synth_of_I_J S _ (upperSquare_commutes_I S u v)
    (upperSquare_commutes_J S u v)

theorem scalarProjection_hyperWeyl_zero (S : QuaternionicStructure E)
    (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
    (hW : HyperWeylFiber S W) (u v : E) : scalarProjection S (W u v) = 0 := by
  rcases hW with ⟨_, _, hI, hJ, _, _⟩
  apply scalarProjection_eq_zero_of_commutes
  apply commutes_synth_of_I_J
  · intro w
    exact congrArg (fun A : E →L[ℝ] E => A w) (hI u v)
  · intro w
    exact congrArg (fun A : E →L[ℝ] E => A w) (hJ u v)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem sp1Formula_of_decomposition
    (S : QuaternionicStructure E)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (D : CompatibleTangentConnection Q)
    (h : KSWEq38Decomposition S Q D) : KSWSp1CurvatureFormula S Q D := by
  intro p y u v hy
  obtain ⟨W, hW, hR⟩ := h p y hy
  rw [hR u v, map_add, map_smul, map_add, sourceRH,
    scalarProjection_synth, sourceREOperator, map_smul,
    scalarProjection_upperSquare_zero, smul_zero, add_zero,
    scalarProjection_hyperWeyl_zero S W hW, add_zero]

/-- Exact implication between the two original model-universal predicates. -/
theorem kswSp1_of_kswDecomposition
    (h : KSWEq38OnModel (E := E) (M := M)) :
    KSWLemma310OnModel (E := E) (M := M) := by
  intro S Q G hn
  exact sp1Formula_of_decomposition S Q G.connection (h S Q G hn)

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWScalarFromDecomposition

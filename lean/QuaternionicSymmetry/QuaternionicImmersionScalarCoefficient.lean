import QuaternionicSymmetry.QuaternionicProjectedConnection
import QuaternionicSymmetry.QuaternionicAlgebraicKSWDecomposition
import QuaternionicSymmetry.ManifoldQuaternionicKSWScalarFromDecomposition

/-! A quaternionic isometric curvature injection preserves the reduced
scalar coefficient of the internally proved scalar/Weyl decomposition. -/
namespace QuaternionicSymmetry.QuaternionicImmersionScalarCoefficient
open QuaternionicKSWModelAlgebra QuaternionicKSWModelRicci QuaternionicKSWUpperModel
open QuaternionicStandardSolderSquare QuaternionicProjectedConnection
open QuaternionicRangeFrameCoordinates QuaternionicFrameInjectionSpan
open QuaternionicLieAlgebraProjection ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarFromDecomposition
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
variable (S : QuaternionicStructure F) (Q : QuaternionicStructure E) (B : F →L[ℝ] E)
  (hB : ∀ v w, inner ℝ (B v) (B w) = inner ℝ v w)
  (hI : ∀ v, B (S.I v) = Q.I (B v)) (hJ : ∀ v, B (S.J v) = Q.J (B v))

include hB hI hJ in
theorem model_intertwines (u v w : F) :
    B (scalarModelR0 S u v w) = scalarModelR0 Q (B u) (B v) (B w) := by
  have hK (a : F) : B (S.K a) = Q.K (B a) := generator_intertwines S Q B hI hJ 2 a
  simp only [model_apply,compactWedgeSum,map_add,map_sub,map_smul,hI,hJ,hK]
  simp only [← hI,← hJ,← hK,hB]

include hI hJ in
theorem compression_commutes (A : E →L[ℝ] E)
    (hAI : ∀ v, A (Q.I v) = Q.I (A v))
    (hAJ : ∀ v, A (Q.J v) = Q.J (A v)) :
    scalarProjection S ((B.adjoint.comp A).comp B) = 0 := by
  apply scalarProjection_eq_zero_of_commutes
  apply commutes_synth_of_I_J
  · intro v
    change B.adjoint (A (B (S.I v))) = S.I (B.adjoint (A (B v)))
    rw [hI,hAI]
    exact adjoint_generator S Q B hI hJ 0 _
  · intro v
    change B.adjoint (A (B (S.J v))) = S.J (B.adjoint (A (B v)))
    rw [hJ,hAJ]
    exact adjoint_generator S Q B hI hJ 1 _

include hB hI hJ in
theorem coefficient_eq
    (R W : F →L[ℝ] F →L[ℝ] F →L[ℝ] F)
    (T V : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (a b : ℝ)
    (hW : HyperWeylFiber S W) (hV : HyperWeylFiber Q V)
    (hR : ∀ u v, R u v = a • scalarModelR0 S u v + W u v)
    (hT : ∀ u v, T u v = b • scalarModelR0 Q u v + V u v)
    (hRT : ∀ u v w, T (B u) (B v) (B w) = B (R u v w)) : a = b := by
  obtain ⟨u,hu⟩ := exists_ne (0 : F)
  have he : a • scalarModelR0 S u (S.I u) + W u (S.I u) =
      b • scalarModelR0 S u (S.I u) +
        (B.adjoint.comp (V (B u) (B (S.I u)))).comp B := by
    ext w
    have h := congrArg B.adjoint (hRT u (S.I u) w)
    rw [adjoint_left_inverse B hB,hR,hT] at h
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,map_add,map_smul,
      ← model_intertwines S Q B hB hI hJ,adjoint_left_inverse B hB] at h
    exact h.symm
  have hp := congrArg (scalarProjection S) he
  rw [map_add,map_smul,scalarProjection_hyperWeyl_zero S W hW,
    map_add,map_smul,compression_commutes S Q B hI hJ _
      (fun w => congrArg (fun A : E →L[ℝ] E => A w) (hV.2.2.1 (B u) (B (S.I u))))
      (fun w => congrArg (fun A : E →L[ℝ] E => A w) (hV.2.2.2.1 (B u) (B (S.I u)))),
    add_zero,add_zero] at hp
  simp only [scalarModelR0,map_sub,map_smul,scalarProjection_synth,
    scalarProjection_upperSquare_zero,sub_zero] at hp
  have hc := congrArg (fun A : F →L[ℝ] F => coeff S A 0) hp
  simp only [map_smul,coeff_synth,Pi.smul_apply,smul_eq_mul,quaternionicGenerator,
    Matrix.cons_val_zero] at hc
  change a * (-2 * inner ℝ (S.I u) (S.I u)) = b * (-2 * inner ℝ (S.I u) (S.I u)) at hc
  rw [S.I.inner_map_map] at hc
  have hpos : 0 < inner ℝ u u := real_inner_self_pos.mpr hu
  nlinarith

end
end QuaternionicSymmetry.QuaternionicImmersionScalarCoefficient

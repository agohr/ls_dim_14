import QuaternionicSymmetry.GeneralComplexAdjointDifferentialSource

/-! Source-free chain of Lee's general adjoint derivative along an actual
real-smooth Lie-group homomorphism. The parameter group may in particular be
the selected compact torus; no character or root relation is assumed. -/

namespace QuaternionicSymmetry.GeneralComplexAdjointTorusChain

open GeneralComplexAdjointDifferentialSource ComplexLieRealCompanion
open scoped Manifold ContDiff
noncomputable section

variable {F T V G : Type}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [Group T] [TopologicalSpace T] [ChartedSpace F T]
  [IsManifold 𝓘(ℝ,F) ∞ T] [LieGroup 𝓘(ℝ,F) ∞ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℂ,V) ∞ G]
  [LieGroup 𝓘(ℂ,V) ∞ G]

/-- The derivative of the literal adjoint orbit along an actual smooth
real Lie-group homomorphism is the bracket with its identity derivative.
The bracket is the actual complex `GroupLieAlgebra` bracket in the supplied
complex charts, while the chain rule is in their canonical real companion. -/
theorem mfderiv_adjointOrbit_comp_lieHom
    (hLee : LeeComplexAdjointDifferentialSource)
    (ρ : T →* G) (hρ : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ ρ)
    (v : GroupLieAlgebra 𝓘(ℂ,V) G)
    (w : TangentSpace 𝓘(ℝ,F) (1 : T)) :
    letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
    letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
    letI : ENat.LEInfty (minSmoothness ℂ 3) := by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
    let u : TangentSpace 𝓘(ℝ,V) (1 : G) :=
      ρ.map_one ▸ mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ρ 1 w
    mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) (fun t => adjointOrbit v (ρ t)) 1 w =
      @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,V) G)
        (GroupLieAlgebra 𝓘(ℂ,V) G) inferInstance u v := by
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
  letI : ENat.LEInfty (minSmoothness ℂ 3) := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
  obtain ⟨hAdDiff,hAdBracket⟩ := hLee (V := V) (G := G) v
  have hρDiff : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,V) ρ 1 :=
    hρ.mdifferentiableAt (by simp)
  have hAdDiff' : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,V)
      (adjointOrbit v) (ρ 1) := by simpa using hAdDiff
  have hChain := mfderiv_comp (x := (1 : T)) hAdDiff' hρDiff
  have hOne : ρ 1 = (1 : G) := ρ.map_one
  let u : TangentSpace 𝓘(ℝ,V) (1 : G) :=
    hOne ▸ mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ρ 1 w
  have hApply := congrArg
    (fun L : TangentSpace 𝓘(ℝ,F) 1 →L[ℝ] V => L w) hChain
  have hMain :
      (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (adjointOrbit v) (ρ 1))
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ρ 1 w) =
        @Bracket.bracket (GroupLieAlgebra 𝓘(ℂ,V) G)
          (GroupLieAlgebra 𝓘(ℂ,V) G) inferInstance
          u v := by
    rw [hOne]
    have hArg : mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ρ 1 w = u := by
      simp [u]
    exact (congrArg
      (fun z : TangentSpace 𝓘(ℝ,V) (1 : G) =>
        (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (adjointOrbit v) 1) z)
      hArg).trans (hAdBracket u)
  have hApply' :
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V)
          (fun t => adjointOrbit v (ρ t)) 1 w =
        (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (adjointOrbit v) (ρ 1))
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) ρ 1 w) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using hApply
  exact hApply'.trans hMain

end
end QuaternionicSymmetry.GeneralComplexAdjointTorusChain

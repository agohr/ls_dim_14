import QuaternionicSymmetry.SelectedTorusWeightDifferentialCoordinates
import QuaternionicSymmetry.IntegralWeightComplexifiedDifferentialSeparation

/-! In the same selected BG-L3 torus Lie atlas, an explicitly real-spanning
family of integral weights gives complexified differentials with trivial
common kernel. The real-spanning hypothesis is not asserted here. -/

namespace QuaternionicSymmetry.SelectedTorusSpanningDifferentials

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusExpDerivativeEquiv
open SelectedTorusWeightDifferentialCoordinates
open SelectedTorusCompactExponentialSmooth
open IntegralWeightComplexifiedDifferentialSeparation
open IntegralWeightRealSpanComplexSeparation
open TorusWeightCharacterDifferentialLinear
open RealToComplexTangentComplexification
open ManifoldQuaternionicTorusAction
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ} {ι : Type*}

theorem selected_character_differentials_separate_of_real_span
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Torus r) G T.hom d)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (μ : ι → Fin r → ℤ)
    (hSpan : Submodule.span ℝ
      (Set.range (fun i => realWeightVector (μ i))) = ⊤)
    (t : ℂ ⊗[ℝ] (Fin d → ℝ)) :
    letI := g.charts
    (∀ i, complexifiedMapComplex
      (weightCharacterDifferentialLinear (μ i) g.charts) t = 0) → t = 0 := by
  classical
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := g.lieGroup
  let B : (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ)
      (circleExpPi r) 0).toLinearMap
  have hBij : Function.Bijective B :=
    circleExpPi_derivative_bijective T g hClosed hImm hLee
  let e : (Fin r → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
    LinearEquiv.ofBijective B hBij
  let bR : Module.Basis (Fin r) ℝ (Fin d → ℝ) :=
    (Pi.basisFun ℝ (Fin r)).map e
  have hCoord (i : ι) (j : Fin r) :
      weightCharacterDifferentialLinear (μ i) g.charts (bR j) =
        Complex.I * (μ i j : ℂ) := by
    simpa [bR, e, B, Pi.basisFun_apply] using
      (weightCharacterDifferential_comp_exp_single T g hClosed hImm hLee
        (μ i) j)
  intro ht
  exact complexified_differentials_separate_of_real_span
    μ bR (fun i => weightCharacterDifferentialLinear (μ i) g.charts)
    hCoord hSpan t ht

end
end QuaternionicSymmetry.SelectedTorusSpanningDifferentials

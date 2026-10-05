import QuaternionicSymmetry.SelectedTorusAtlasDimensionExact
import QuaternionicSymmetry.SelectedTorusCompactExponentialDerivative
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The literal coordinatewise circle exponential has an invertible real
differential at zero in the SAME selected BG-L3 embedded torus atlas. -/

namespace QuaternionicSymmetry.SelectedTorusExpDerivativeEquiv

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusAtlasDimensionExact
open SelectedTorusCompactInclusionSmooth
open SelectedTorusCompactExponentialSmooth
open SelectedTorusCompactExponentialLift
open SelectedTorusCompactExponentialDerivative
open ComplexTorusRealChartDerivative
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ComplexLieRealCompanion ComplexTorusLieGroup
open ComplexTorusCharacterHolomorphic
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ManifoldComplexHolomorphicFactorization
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  {r d : ℕ}

theorem circleExpPi_derivative_bijective
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Fin r → Circle) G T.hom d)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem) :
    letI := g.charts
    Function.Bijective
      (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ)
        (circleExpPi r) 0) := by
  letI : ChartedSpace (Fin d → ℝ) (Fin r → Circle) := g.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Fin r → Circle) := g.lieGroup
  letI : T2Space (ComplexTorus r) :=
    (torusVal_isOpenEmbedding r).t2Space
  letI : SecondCountableTopology (ComplexTorus r) :=
    (torusVal_isOpenEmbedding r).secondCountableTopology
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realManifold
  letI : LieGroup 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realLieGroup
  have hExp := circleExpPi_smooth_selected T g hClosed hImm hLee
  have hInc := compactInclusion_smooth T g hClosed hImm hLee
  have hVal : ContMDiff 𝓘(ℝ,Fin r → ℂ) 𝓘(ℝ,Fin r → ℂ) ∞
      (torusVal r) :=
    holomorphic_is_real_smooth (contMDiff_torusVal r)
  have hcomp1 := mfderiv_comp (I := 𝓘(ℝ,Fin r → ℝ))
    (I' := 𝓘(ℝ,Fin d → ℝ)) (I'' := 𝓘(ℝ,Fin r → ℂ))
    (x := (0 : Fin r → ℝ))
    (hInc.mdifferentiableAt (by simp))
    (hExp.mdifferentiableAt (by simp))
  rw [circleExpPi_zero] at hcomp1
  have hcomp2 := mfderiv_comp (I := 𝓘(ℝ,Fin r → ℝ))
    (I' := 𝓘(ℝ,Fin r → ℂ)) (I'' := 𝓘(ℝ,Fin r → ℂ))
    (x := (0 : Fin r → ℝ))
    (hVal.mdifferentiableAt (by simp))
    ((hInc.comp hExp).mdifferentiableAt (by simp))
  rw [torusVal_mfderiv_eq_id] at hcomp2
  have hAmb : mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin r → ℂ)
      (torusVal r ∘ (compactInclusion r ∘ circleExpPi r)) 0 =
      imaginaryCoordinateMap r := by
    rw [mfderiv_eq_fderiv]
    exact (compactExp_ambient_hasFDerivAt_zero r).fderiv
  have hFactor : imaginaryCoordinateMap r =
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ)
        (compactInclusion r) 1).comp
      (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ)
        (circleExpPi r) 0) := by
    calc
      imaginaryCoordinateMap r =
          mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin r → ℂ)
            (torusVal r ∘ (compactInclusion r ∘ circleExpPi r)) 0 := hAmb.symm
      _ = mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin r → ℂ)
            (compactInclusion r ∘ circleExpPi r) 0 := by
              simpa only [ContinuousLinearMap.id_comp] using hcomp2
      _ = _ := hcomp1
  let B : (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ)
      (circleExpPi r) 0).toLinearMap
  have hInj : Function.Injective B := by
    intro a b hab
    apply imaginaryCoordinateMap_injective r
    rw [hFactor]
    change (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ)
      (compactInclusion r) 1) (B a) =
      (mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,Fin r → ℂ)
        (compactInclusion r) 1) (B b)
    exact congrArg _ hab
  have hDim := selected_atlas_dimension_eq_rank T g hClosed hImm hLee
  have hFinrank : Module.finrank ℝ (Fin r → ℝ) =
      Module.finrank ℝ (Fin d → ℝ) := by simp [hDim]
  have hSurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hFinrank).mp hInj
  exact ⟨hInj,hSurj⟩

end
end QuaternionicSymmetry.SelectedTorusExpDerivativeEquiv

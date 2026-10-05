import QuaternionicSymmetry.FourDimensionalHalfSpinActualTransition
import QuaternionicSymmetry.ManifoldTwistorSphereSmoothTransition

/-! C∞ regularity of the *literal matrix-defined* CP¹ transitions on actual
adapted tangent overlaps. Smoothness is checked by the independently proved
Hopf diffeomorphism and the already smooth rank-three sphere transition;
the latter is a proof device, not the definition of the projective action. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinActualTransitionSmooth

open scoped ContDiff Manifold Quaternion
open FourDimensionalHalfSpinActualTransition
  FourDimensionalHalfSpinHopfDiffeomorphPackage
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinHopfProjectiveDescent
  FourDimensionalHalfSpinProjective
  QuaternionicProjectiveStandardHilbertStructure
  QuaternionicManifoldPointwiseLifts
  QuaternionicManifoldRotationCoordinates
  ManifoldTwistorSphereCore
  ManifoldTwistorSphereBundle
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorSphereSmoothTransition
  FourDimensionalTwistorNormalizerQuotient
  QuaternionicIsometryNormalizer

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

def spinorCoordChange (i j : atlas ℍ M) (p : M × ProjectiveSpinor) :
    ProjectiveSpinor := by
  classical
  exact if h : p.1 ∈ Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet j then
    spinorTransition Q i j p.1 h.1 h.2 p.2
  else p.2

theorem hopf_transition_eq (i j : atlas ℍ M) (p : M × ProjectiveSpinor)
    (hp : p.1 ∈ Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet j) :
    projectiveHopfGeometric (spinorCoordChange Q i j p) =
      euclideanSphereCoordChange Q i j p.1 (projectiveHopfGeometric p.2) := by
  have hp' : p.1 ∈ (Q.frames.adaptedCore.localTriv i).baseSet ∩
      (Q.frames.adaptedCore.localTriv j).baseSet := hp
  have htr : spinorCoordChange Q i j p =
      spinorTransition Q i j p.1 hp.1 hp.2 p.2 := by
    dsimp [spinorCoordChange]
    rw [dif_pos hp']
  rw [htr]
  apply Subtype.ext
  change ManifoldTwistorCoefficientSphere.toEuclidean
      (projectiveHopf (spinorTransition Q i j p.1 hp.1 hp.2 p.2)).1 =
    (euclideanSphereCoordChange Q i j p.1 (projectiveHopfGeometric p.2)).1
  rw [spinorTransition_hopf Q i j p.1 hp.1 hp.2 p.2]
  dsimp [euclideanSphereCoordChange]
  rw [dif_pos hp']
  change ManifoldTwistorCoefficientSphere.toEuclidean
      (rotationLinear leftLineStructure
        (fixedTransitionNormalizer leftLineStructure Q i j p.1 hp.1 hp.2)
        (projectiveHopf p.2).1) =
    ManifoldTwistorCoefficientSphere.toEuclidean
      (Q.reduction.rankThreeCoordChange i j p.1
        ((coefficientSphereHomeomorph.symm (projectiveHopfGeometric p.2)).1))
  rw [rotationLinear_fixedTransition]
  rfl

theorem spinorCoordChange_contMDiffOn (i j : atlas ℍ M) :
    ContMDiffOn
      (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ))
      𝓘(ℝ, Fin 1 → ℂ) ∞
      (spinorCoordChange Q i j)
      ((Q.frames.adaptedCore.baseSet i ∩
        Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ) := by
  let S : Set (M × ProjectiveSpinor) :=
    (Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ
  have hpair : ContMDiff
      (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ))
      (𝓘(ℝ, ℍ).prod (𝓡 2)) ∞
      (fun p : M × ProjectiveSpinor =>
        (p.1, projectiveHopfGeometric p.2)) := by
    exact contMDiff_fst.prodMk
      (projectiveHopfGeometricDiffeomorph.contMDiff_toFun.comp contMDiff_snd)
  have hmem : ∀ p ∈ S,
      (p.1, projectiveHopfGeometric p.2) ∈
        ((Q.frames.adaptedCore.baseSet i ∩
          Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ) := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  have hsphere : ContMDiffOn
      (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)) (𝓡 2) ∞
      (fun p : M × ProjectiveSpinor =>
        euclideanSphereCoordChange Q i j p.1
          (projectiveHopfGeometric p.2)) S :=
    (sphereCoordChange_contMDiffOn Q i j).comp hpair.contMDiffOn hmem
  have hinv : ContMDiffOn
      (𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ))
      𝓘(ℝ, Fin 1 → ℂ) ∞
      (fun p : M × ProjectiveSpinor =>
        projectiveHopfGeometricDiffeomorph.symm
          (euclideanSphereCoordChange Q i j p.1
            (projectiveHopfGeometric p.2))) S :=
    projectiveHopfGeometricDiffeomorph.symm.contMDiff_toFun.comp_contMDiffOn hsphere
  apply hinv.congr
  intro p hp
  have h := congrArg projectiveHopfGeometricDiffeomorph.symm
    (hopf_transition_eq Q i j p hp.1)
  change projectiveHopfGeometricDiffeomorph.symm
      (projectiveHopfGeometricDiffeomorph (spinorCoordChange Q i j p)) = _ at h
  rw [projectiveHopfGeometricDiffeomorph.symm_apply_apply] at h
  exact h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinActualTransitionSmooth

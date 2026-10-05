import QuaternionicSymmetry.ManifoldTwistorProjectiveAmpleness
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
import QuaternionicSymmetry.ManifoldTwistorSectionComparison
import QuaternionicSymmetry.HolomorphicLineCoreAmpleness

/-! Transfer the actual twistor contact-line tensor powers, sections, and
complete projective maps to the generic represented holomorphic line-core
framework used by the analytic Demailly section estimate. -/

namespace QuaternionicSymmetry.ManifoldTwistorAmpleCoreBridge

open QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
open QuaternionicSymmetry.ManifoldTwistorLineCoreClasses
open QuaternionicSymmetry.ManifoldTwistorProjectiveAmpleness
open QuaternionicSymmetry.ManifoldTwistorLinearSystem
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A)

/-- The positive integer twist and the generic scalar-cocycle tensor power
are definitionally the same actual core after the checked integer-power
identity. -/
theorem integerTwist_eq_contactPowerCore (k : ℕ) :
    letI := A.charts
    L.integerTwistCore Q D (k : ℤ) =
      (powerCoreRep 𝓘(ℂ, ComplexTwistorModel n)
        (contactLineCore Q D L) k).core := by
  simpa [contactLineCore, powerCoreRep] using
    L.integerTwistCore_natCast Q D k

/-- The two bundled holomorphic-section spaces of this same positive
tensor-power core are canonically pointwise linearly equivalent. -/
def bundledPositiveTwistEquiv (k : ℕ) :
    letI := A.charts
    HolomorphicTwistSections Q D L (k : ℤ) ≃ₗ[ℂ]
      HolomorphicLineCorePullback.GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D L) k) := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D (k : ℤ)
  let P := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore Q D L) k
  letI := P.holomorphic
  have hCore := integerTwist_eq_contactPowerCore Q D L k
  unfold HolomorphicTwistSections HolomorphicLineCorePullback.GlobalSections
  rw [hCore]

/-- Complex-linear identification of the original coefficient presentation
with genuine bundled sections of the generic represented power core. -/
def coefficientPositiveTwistEquiv (k : ℕ) :
    letI := A.charts
    ManifoldTwistorLinearSystem.GlobalSections Q D L (k : ℤ) ≃ₗ[ℂ]
      HolomorphicLineCorePullback.GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D L) k) := by
  letI := A.charts
  exact (globalCoefficientSectionsEquiv Q D L (k : ℤ)).trans
    (bundledPositiveTwistEquiv Q D L k)

theorem coefficientPositiveTwistEquiv_apply (k : ℕ)
    (s : ManifoldTwistorLinearSystem.GlobalSections Q D L (k : ℤ))
    (x : SphereBundleTotal Q) :
    letI := A.charts
    coefficientPositiveTwistEquiv Q D L k s x =
      s.1 ⟨x, Set.mem_univ x⟩ := by
  letI := A.charts
  unfold coefficientPositiveTwistEquiv bundledPositiveTwistEquiv
  simp [globalCoefficientSectionsEquiv]
  rfl

/-- Generation passes through the pointwise section equivalence. -/
theorem genericGenerated_of_twistorGenerated (k : ℕ)
    (hGen : GloballyGeneratedTwist Q D L (k : ℤ)) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D L) k) := by
  letI := A.charts
  intro x
  obtain ⟨s, hs⟩ := hGen x
  refine ⟨coefficientPositiveTwistEquiv Q D L k s, ?_⟩
  rw [coefficientPositiveTwistEquiv_apply]
  exact hs

/-- The transported basis has exactly the same evaluation coordinates,
not merely projectively proportional ones. -/
theorem transportedBasisEvaluation_eq (k d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ
      (ManifoldTwistorLinearSystem.GlobalSections Q D L (k : ℤ)))
    (x : SphereBundleTotal Q) :
    letI := A.charts
    HolomorphicLineCoreProjectiveEvaluation.basisEvaluation
      𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D L) k) d
      (b.map (coefficientPositiveTwistEquiv Q D L k)) x =
    ManifoldTwistorProjectiveBasisCoordinates.basisEvaluation
      Q D L (k : ℤ) d b x := by
  letI := A.charts
  funext i
  exact coefficientPositiveTwistEquiv_apply Q D L k (b i) x

/-- Under an actual basepoint-free twistor system, the two full projective
maps are pointwise identical in the same homogeneous coordinates. -/
theorem transportedProjectiveMap_eq (k d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ
      (ManifoldTwistorLinearSystem.GlobalSections Q D L (k : ℤ)))
    (hBase : ManifoldTwistorLinearSystem.baseLocus Q D L (k : ℤ) = ∅)
    (hGen : letI := A.charts
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D L) k)) :
    letI := A.charts
    projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D L) k) d
      (b.map (coefficientPositiveTwistEquiv Q D L k)) hGen =
    ManifoldTwistorProjectiveBasisCoordinates.basisProjectiveEvaluationTotal
      Q D L (k : ℤ) d b := by
  letI := A.charts
  funext x
  have hx : x ∉ ManifoldTwistorLinearSystem.baseLocus Q D L (k : ℤ) := by
    simp [hBase]
  rw [ManifoldTwistorProjectiveBasisCoordinates.basisProjectiveEvaluationTotal_eq
    Q D L (k : ℤ) d b x hx]
  change Projectivization.mk ℂ
      (HolomorphicLineCoreProjectiveEvaluation.basisEvaluation
        𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D L) k) d
        (b.map (coefficientPositiveTwistEquiv Q D L k)) x) _ =
    Projectivization.mk ℂ
      (ManifoldTwistorProjectiveBasisCoordinates.basisEvaluation
        Q D L (k : ℤ) d b x) _
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨1, ?_⟩
  simpa using (transportedBasisEvaluation_eq Q D L k d b x).symm

/-- Genuine very ampleness of the twistor coefficient system transfers to
the same positive power as a generic represented line core. The complete
maps are equal, so their topological embedding and derivative hypotheses
are transported without a separate source theorem. -/
theorem veryAmpleCore_of_twistorVeryAmple (k : ℕ)
    (hVery : VeryAmpleTwist Q D L k) :
    letI := A.charts
    letI := A.complexManifold
    VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D L) k) := by
  letI := A.charts
  letI := A.complexManifold
  obtain ⟨d, b, hBase, hEmbed, hDeriv⟩ := hVery
  let hTwGen : GloballyGeneratedTwist Q D L (k : ℤ) :=
    (globallyGeneratedTwist_iff_baseLocus_empty Q D L (k : ℤ)).2 hBase
  let hGen := genericGenerated_of_twistorGenerated Q D L k hTwGen
  let e := coefficientPositiveTwistEquiv Q D L k
  let b' := b.map e
  have hMap :
      projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D L) k) d b' hGen =
      ManifoldTwistorProjectiveBasisCoordinates.basisProjectiveEvaluationTotal
        Q D L (k : ℤ) d b :=
    transportedProjectiveMap_eq Q D L k d b hBase hGen
  refine ⟨d, b', hGen, ?_, ?_⟩
  · rw [hMap]
    exact hEmbed
  · intro x
    rw [hMap]
    exact hDeriv x

/-- The twistor's actual contact-line ampleness and generic represented
core ampleness are the same geometric property in these coordinates. -/
theorem ampleCore_of_ampleContactLine
    (hAmple : AmpleContactLine Q D L) :
    letI := A.charts
    letI := A.complexManifold
    AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D L) := by
  letI := A.charts
  letI := A.complexManifold
  obtain ⟨k, hk, hVery⟩ := hAmple
  exact ⟨k, hk, veryAmpleCore_of_twistorVeryAmple Q D L k hVery⟩

end
end QuaternionicSymmetry.ManifoldTwistorAmpleCoreBridge

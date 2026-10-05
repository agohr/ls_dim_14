import QuaternionicSymmetry.ManifoldQuaternionicContactPowerSectionAction
import QuaternionicSymmetry.ManifoldQuaternionicContactFiniteSections

/-! Cartan–Serre finiteness and one consistent finite-basis norm on every
complete holomorphic contact-power section space. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerFiniteSections

open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldQuaternionicSpanSymmetry
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open HolomorphicLineFiniteSectionsSource FiniteDimensionalComplexModuleNorm
open HolomorphicLineCoreBasisOrbitContinuity
open ManifoldQuaternionicContactPowerSectionAction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem finiteDimensional_contactPowerSections
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ) :
    letI := B.charts
    FiniteDimensional ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k)) := by
  letI := B.charts
  letI := B.complexManifold
  exact hFinite (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore Q D C.line) k)

def contactPowerSectionsNormedAddCommGroup
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ) :
    letI := B.charts
    NormedAddCommGroup
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k)) := by
  letI := B.charts
  letI := finiteDimensional_contactPowerSections Q hFinite D B C k
  exact normedAddCommGroup _

def contactPowerSectionsNormedSpace
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ) :
    letI := B.charts
    letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
    NormedSpace ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k)) := by
  letI := B.charts
  letI := finiteDimensional_contactPowerSections Q hFinite D B C k
  letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
  exact normedSpace _

theorem continuous_contactPowerAction_of_basis_orbits
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hOrbit :
      letI := B.charts
      letI := finiteDimensional_contactPowerSections Q hFinite D B C k
      letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
      ∀ (i : Fin (Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
            (contactLineCore Q D C.line) k))))
        (z : ManifoldTwistorSphereCore.SphereBundleTotal Q),
        Continuous (fun f : QuaternionicIsometries Q =>
          (contactPowerSectionRepresentation Q D B C k f
            ((Module.finBasis ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
              (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                (contactLineCore Q D C.line) k))) i)) z)) :
    letI := B.charts
    letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
    Continuous (fun p : QuaternionicIsometries Q ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) =>
      contactPowerSectionRepresentation Q D B C k p.1 p.2) := by
  letI := B.charts
  letI := finiteDimensional_contactPowerSections Q hFinite D B C k
  letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
  letI := contactPowerSectionsNormedSpace Q hFinite D B C k
  exact continuous_action_of_basis_orbits
    𝓘(ℂ,ComplexTwistorModel n)
    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line) k)
    (contactPowerSectionRepresentation Q D B C k) hOrbit

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerFiniteSections

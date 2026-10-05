import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicContact
import QuaternionicSymmetry.ManifoldTwistorNijenhuis

/-! A bracket criterion for the nondegeneracy of the actual horizontal
contact distribution. Since the contact form annihilates horizontal
directions, its exterior derivative on horizontal fields is minus the
form applied to their Lie bracket. The condition below uses the genuine
manifold bracket and the source holomorphic line, rather than an
unrelated alternating form. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev RealModel := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The Levi bracket of the checked smooth horizontal distribution is
nondegenerate at every twistor point. The extensions are genuine smooth
horizontal vector fields on the actual sphere total space. -/
def HolomorphicContactData.IsContactNondegenerate {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (C : HolomorphicContactData Q D n A) : Prop :=
  ∀ (z : SphereBundleTotal Q)
    (u : horizontalTangentSubmodule Q D z), u ≠ 0 →
      ∃ U : Set (SphereBundleTotal Q), IsOpen U ∧ z ∈ U ∧
      ∃ V W : ∀ y : SphereBundleTotal Q,
          TangentSpace (RealModel (E := E)) y,
        ContMDiffOn (RealModel (E := E)) (RealModel (E := E)).tangent ∞
          (fun y => (⟨y,V y⟩ : TangentBundle (RealModel (E := E))
            (SphereBundleTotal Q))) U ∧
        ContMDiffOn (RealModel (E := E)) (RealModel (E := E)).tangent ∞
          (fun y => (⟨y,W y⟩ : TangentBundle (RealModel (E := E))
            (SphereBundleTotal Q))) U ∧
        (∀ y ∈ U, V y ∈ horizontalTangentSubmodule Q D y) ∧
        (∀ y ∈ U, W y ∈ horizontalTangentSubmodule Q D y) ∧
        V z = u.1 ∧
        C.line.contactFormReal Q D z
          (VectorField.mlieBracket (RealModel (E := E)) V W z) ≠ 0

/-- The precise contact nondegeneracy conclusion to be supplied by
LeBrun's theorem, separate from the already derived horizontal kernel
and the explicitly stated holomorphicity of the contact form. -/
structure NondegenerateHolomorphicContactData (n : ℕ)
    (A : CompatibleComplexAtlas Q D n) where
  contact : HolomorphicContactData Q D n A
  nondegenerate : contact.IsContactNondegenerate Q D

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

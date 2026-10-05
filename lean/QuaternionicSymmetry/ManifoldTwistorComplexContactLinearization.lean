import QuaternionicSymmetry.HolomorphicLineFamilyJointHolomorphic
import QuaternionicSymmetry.ManifoldTwistorComplexContactFiberJointWitness
import QuaternionicSymmetry.HolomorphicLineComplexTorusLinearizationAction
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

/-! The canonical derivative action of the actual complexified torus is a
holomorphic linearization on the entire original contact-line bundle. The
fiber maps and their laws come from contact-form descent; local nonzero
sections prove joint holomorphicity on the independently charted total space.
No projective character shift or algebraic comparison is assumed here. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexContactLinearization

open ManifoldTwistorComplexContactFiberJointWitness
open ManifoldTwistorContactAutomorphismFiber ManifoldTwistorComplexContactAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLineCoreClasses HolomorphicLineComplexTorusLinearization
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)
  {r : ℕ} (A : ContinuousTorusAction Q r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
    ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z)

/-- Joint holomorphicity of the canonical contact action on all fibers,
including the zero section. -/
theorem contactFiberEquiv_total_joint_holomorphic :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.holomorphic
    ContMDiff
      (𝓘(ℂ,Fin r → ℂ).prod (𝓘(ℂ,ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)))
      (𝓘(ℂ,ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)) ∞
      (fun p : ComplexTorus r × Bundle.TotalSpace ℂ C.line.core.Fiber =>
        (⟨ρ p.1 p.2.1, contactFiberEquiv Q D B C.line
          (complexContactAction Q D B C A ρ hJoint hRestrict p.1)
          p.2.1 p.2.2⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber)) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  exact HolomorphicLineFamilyJointHolomorphic.contMDiff_totalMap_of_local_sections
    𝓘(ℂ,Fin r → ℂ) 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
    C.line.core C.line.core
    (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2)
    (fun t z => (contactFiberEquiv Q D B C.line
      (complexContactAction Q D B C A ρ hJoint hRestrict t) z).toLinearMap)
    hJoint (fun _ z => exists_local_nonzero_joint_section Q D B C A ρ hJoint hRestrict z)

/-- The selected point action lifts canonically to a genuine holomorphic
linearization of the same original contact line. -/
def actualContactLineLinearization :
    letI := B.charts
    ComplexTorusLineLinearization (contactLineCore Q D C.line) (r := r) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  let χ := complexContactAction Q D B C A ρ hJoint hRestrict
  refine {
    baseAction := ρ
    fiberEquiv := fun t z => contactFiberEquiv Q D B C.line (χ t) z
    one_total := ?_
    mul_total := ?_
    joint_holomorphic := contactFiberEquiv_total_joint_holomorphic
      Q D B C A ρ hJoint hRestrict }
  · intro v
    change (⟨(χ 1).1 v.1, contactFiberMap Q D B C.line (χ 1) v.1 v.2⟩ :
      Bundle.TotalSpace ℂ C.line.core.Fiber) = v
    rw [map_one, contactFiberMap_one]
    rfl
  · intro s t v
    change (⟨(χ (s*t)).1 v.1,
        contactFiberMap Q D B C.line (χ (s*t)) v.1 v.2⟩ :
      Bundle.TotalSpace ℂ C.line.core.Fiber) =
      ⟨(χ s).1 ((χ t).1 v.1),
        contactFiberMap Q D B C.line (χ s) ((χ t).1 v.1)
          (contactFiberMap Q D B C.line (χ t) v.1 v.2)⟩
    rw [map_mul, contactFiberMap_mul]
    rfl

/-- The constructed linearization retains the literal original point
action, without selecting a new torus. -/
theorem actualContactLineLinearization_baseAction :
    letI := B.charts
    (actualContactLineLinearization Q D B C A ρ hJoint hRestrict).baseAction = ρ := rfl

end
end QuaternionicSymmetry.ManifoldTwistorComplexContactLinearization

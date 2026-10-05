import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismIsometrySections
import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismFiberOrbit
import QuaternionicSymmetry.ComplexTorusCharacterHolomorphic

/-! The canonical full-contact-group action has exactly the integral
weights of the original compact isometry action. Holomorphic uniqueness
on the actual orbit-pullback line proves the complex-character formula;
no equivariance or canonical-linearization premise is added. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexContactEigenSections

open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorContactAutomorphismSections
open ManifoldTwistorContactAutomorphismIsometrySections
open ManifoldTwistorContactAutomorphismFiberOrbit ManifoldTwistorComplexContactAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses HolomorphicLineCoreClasses
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open HolomorphicLineCorePullback HolomorphicLineCorePullbackLocalSections
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ComplexTorusCharacterHolomorphic TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)
  {r : ℕ} (A : ContinuousTorusAction Q r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ, ComplexTwistorModel n))
      𝓘(ℂ, ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
    ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z)

theorem contactFiberEquiv_eigenSection (μ : Fin r → ℤ)
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line))
    (hs : letI := B.charts
      ∀ t : Torus r,
        ManifoldQuaternionicIsometryContactSections.contactSectionEquiv Q D B C
          (A.representation t) s = (weightCharacter μ t : ℂ) • s)
    (g : ComplexTorus r) (z : SphereBundleTotal Q) :
    contactFiberEquiv Q D B C.line
        (complexContactAction Q D B C A ρ hJoint hRestrict g) z (s z) =
      (complexWeightCharacter μ g : ℂ) • s (ρ g z) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  let IB := 𝓘(ℂ, ComplexTwistorModel n)
  let IT := 𝓘(ℂ, Fin r → ℂ)
  let L := contactLineCore Q D C.line
  let f : ComplexTorus r → SphereBundleTotal Q := fun a => ρ a z
  have hf : ContMDiff IT IB ∞ f :=
    hJoint.comp (contMDiff_id.prodMk contMDiff_const)
  let K := pullbackLineCore IB IT L f hf
  letI := K.holomorphic
  let u : ∀ a, K.core.Fiber a := fun a =>
    contactFiberEquiv Q D B C.line
      (complexContactAction Q D B C A ρ hJoint hRestrict a) z (s z)
  let U : GlobalSections IT K :=
    ⟨u, contMDiffOn_univ.mp
      (alongMap_contMDiffOn_pullback IB IT C.line.core f hf Set.univ u
        (contactFiberEquiv_orbit_holomorphic Q D B C A ρ hJoint hRestrict
          z (s z)).contMDiffOn)⟩
  let S : GlobalSections IT K := restrictionLinear IB IT L f hf s
  let V : GlobalSections IT K :=
    ⟨fun a => (complexWeightCharacter μ a : ℂ) • S a,
      (complexWeightCharacter_holomorphic μ).smul_section S.contMDiff⟩
  have hcompact : ∀ t : Torus r, (U - V) (compactInclusion r t) = 0 := by
    intro t
    apply sub_eq_zero.mpr
    change contactFiberEquiv Q D B C.line
        (complexContactAction Q D B C A ρ hJoint hRestrict
          (compactInclusion r t)) z (s z) =
      (complexWeightCharacter μ (compactInclusion r t) : ℂ) •
        s (ρ (compactInclusion r t) z)
    rw [complexContactAction_compact, contactFiberEquiv_isometry,
      complexWeightCharacter_compact, hRestrict]
    calc
      contactLineFiberEquiv Q D C.line (A.representation t) z (s z) =
          (ManifoldQuaternionicIsometryContactSections.contactSectionEquiv
            Q D B C (A.representation t) s)
              (sphereTotalMap Q (A.representation t) z) :=
        (ManifoldQuaternionicIsometryContactSections.contactSectionEquiv_apply_at_image
          Q D B C (A.representation t) s z).symm
      _ = (weightCharacter μ t : ℂ) •
          s (sphereTotalMap Q (A.representation t) z) := by
        rw [hs t]
        rfl
  have hz := HolomorphicLineSectionCompactTorusIdentity.zero_of_compact
    K (U - V) hcompact g
  exact sub_eq_zero.mp hz

theorem contactSectionEquiv_eigenSection (μ : Fin r → ℤ)
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line))
    (hs : letI := B.charts
      ∀ t : Torus r,
        ManifoldQuaternionicIsometryContactSections.contactSectionEquiv Q D B C
          (A.representation t) s = (weightCharacter μ t : ℂ) • s)
    (g : ComplexTorus r) :
    letI := B.charts
    contactSectionEquiv Q D B C
        (complexContactAction Q D B C A ρ hJoint hRestrict g) s =
      (complexWeightCharacter μ g : ℂ) • s := by
  letI := B.charts
  apply ContMDiffSection.ext
  intro y
  obtain ⟨z, rfl⟩ := (ρ g).surjective y
  have h := contactSectionEquiv_apply_at_image Q D B C
    (complexContactAction Q D B C A ρ hJoint hRestrict g) s z
  exact h.trans
    (contactFiberEquiv_eigenSection Q D B C A ρ hJoint hRestrict μ s hs g z)

end
end QuaternionicSymmetry.ManifoldTwistorComplexContactEigenSections

import QuaternionicSymmetry.ManifoldTwistorContactAutomorphisms
import QuaternionicSymmetry.ManifoldTwistorContactComplexExact
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Isomorphisms

/-! Canonical contact-line fiber maps for every actual holomorphic contact
automorphism. They are derived by descent of its differential through the
kernel of the actual surjective contact form, not supplied as extra data. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactAutomorphismFiber

open ManifoldTwistorContactAutomorphisms ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (L : HolomorphicContactLine Q D n B)

def contactFiberMap (f : ContactAutomorphisms Q D B L) (z : SphereBundleTotal Q) :
    L.core.Fiber z →ₗ[ℂ] L.core.Fiber (f.1 z) := by
  letI := B.charts
  letI := B.complexManifold
  let θ := L.contactFormComplex Q D z
  let h := (L.contactFormComplex Q D (f.1 z)).comp
    (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n) f.1 z).toLinearMap
  have hk : LinearMap.ker θ ≤ LinearMap.ker h := f.2.1 z
  exact ((LinearMap.ker θ).liftQ h hk).comp
    (θ.quotKerEquivOfSurjective (L.contactFormComplex_surjective Q D z)).symm.toLinearMap

theorem contactFiberMap_contactForm (f : ContactAutomorphisms Q D B L)
    (z : SphereBundleTotal Q) :
    letI := B.charts
    ∀ v : TangentSpace 𝓘(ℂ, ComplexTwistorModel n) z,
      contactFiberMap Q D B L f z (L.contactFormComplex Q D z v) =
        L.contactFormComplex Q D (f.1 z)
          (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n) f.1 z v) := by
  letI := B.charts
  letI := B.complexManifold
  intro v
  simp only [contactFiberMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply,
    ContinuousLinearMap.coe_coe]

theorem contactFiberMap_surjective (f : ContactAutomorphisms Q D B L)
    (z : SphereBundleTotal Q) : Function.Surjective (contactFiberMap Q D B L f z) := by
  letI := B.charts
  letI := B.complexManifold
  intro w
  obtain ⟨u, hu⟩ := L.contactFormComplex_surjective Q D (f.1 z) w
  let T := f.1.mfderivToContinuousLinearEquiv (by simp) z
  refine ⟨L.contactFormComplex Q D z (T.symm u), ?_⟩
  rw [contactFiberMap_contactForm]
  have hT : mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
      f.1 z (T.symm u) = u := T.apply_symm_apply u
  rw [hT, hu]

def contactFiberEquiv (f : ContactAutomorphisms Q D B L) (z : SphereBundleTotal Q) :
    L.core.Fiber z ≃ₗ[ℂ] L.core.Fiber (f.1 z) := by
  letI : FiniteDimensional ℂ (L.core.Fiber z) := by
    change FiniteDimensional ℂ ℂ
    infer_instance
  let F := contactFiberMap Q D B L f z
  have hs : Function.Surjective F := contactFiberMap_surjective Q D B L f z
  have hi : Function.Injective F := LinearMap.injective_iff_surjective.mpr hs
  exact LinearEquiv.ofBijective F ⟨hi, hs⟩

theorem contactFiberEquiv_contactForm (f : ContactAutomorphisms Q D B L)
    (z : SphereBundleTotal Q) :
    letI := B.charts
    ∀ v : TangentSpace 𝓘(ℂ, ComplexTwistorModel n) z,
      contactFiberEquiv Q D B L f z (L.contactFormComplex Q D z v) =
        L.contactFormComplex Q D (f.1 z)
          (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n) f.1 z v) :=
  contactFiberMap_contactForm Q D B L f z

theorem contactFiberMap_one (z : SphereBundleTotal Q) (w : L.core.Fiber z) :
    contactFiberMap Q D B L 1 z w = w := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨v, rfl⟩ := L.contactFormComplex_surjective Q D z w
  rw [contactFiberMap_contactForm]
  change L.contactFormComplex Q D z
    (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
      (id : SphereBundleTotal Q → SphereBundleTotal Q) z v) = _
  rw [mfderiv_id]
  rfl

theorem contactFiberMap_mul (f g : ContactAutomorphisms Q D B L)
    (z : SphereBundleTotal Q) (w : L.core.Fiber z) :
    contactFiberMap Q D B L (f * g) z w =
      contactFiberMap Q D B L f (g.1 z) (contactFiberMap Q D B L g z w) := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨v, rfl⟩ := L.contactFormComplex_surjective Q D z w
  rw [contactFiberMap_contactForm, contactFiberMap_contactForm,
    contactFiberMap_contactForm]
  change L.contactFormComplex Q D (f.1 (g.1 z))
      (mfderiv 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
        (f.1 ∘ g.1) z v) = _
  rw [mfderiv_comp z (f.1.contMDiff.mdifferentiable (by simp) (g.1 z))
    (g.1.contMDiff.mdifferentiable (by simp) z)]
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorContactAutomorphismFiber

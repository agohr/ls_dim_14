import QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Published background: Wells, *Differential Analysis on Complex Manifolds*,
3rd ed., Springer GTM 65, I §3 Theorems 3.7–3.8, pp.34–35.
Restricting the ambient integrable complex structure to invariant smooth
tangent subspaces gives zero Nijenhuis tensor; Newlander–Nirenberg supplies
the compatible complex atlas. The inclusion is complex differentiable.
See Textbooks/STAGE2_FIDELITY_REVIEW_20261001.md for provenance. -/

namespace QuaternionicSymmetry.ComplexSubmanifoldInput

open scoped Manifold ContDiff
noncomputable section

variable {F B : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]
  [TopologicalSpace B] [ChartedSpace F B]

/-- A real embedded atlas on the genuine subset with its inherited
topology. Inclusion is an immersion; its topological embedding is already
the subtype inclusion, not a separately assumed abstract identification. -/
structure RealEmbeddedAtlas (S : Set B) (k : ℕ) where
  charts : ChartedSpace (EuclideanSpace ℝ (Fin k)) S
  manifold : letI := charts
    IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ S
  inclusion_smooth : letI := charts
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,F) ∞
      (Subtype.val : S → B)
  inclusion_injective_derivative : letI := charts
    ∀ x : S, Function.Injective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,F)
        (Subtype.val : S → B) x)

/-- The range of the actual inclusion derivative is stable under ambient
multiplication by `i`. A real subspace with this property is a complex
subspace; no unrelated tangent model is substituted. -/
def RealEmbeddedAtlas.ComplexTangent {S : Set B} {k : ℕ}
    (A : RealEmbeddedAtlas (F := F) S k) : Prop :=
  letI := A.charts
  ∀ (x : S) (v : TangentSpace 𝓘(ℝ,F) x.1),
    v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,F)
        (Subtype.val : S → B) x).toLinearMap →
    Complex.I • (show F from v) ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,F)
        (Subtype.val : S → B) x).toLinearMap

/-- The stated `i`-invariance genuinely equips the derivative range with
complex scalar multiplication, by decomposing each complex scalar into
real and imaginary parts. This algebra is internal to the interface. -/
def RealEmbeddedAtlas.complexTangentSpace {S : Set B} {k : ℕ}
    (A : RealEmbeddedAtlas (F := F) S k) (hA : A.ComplexTangent)
    (x : S) : letI := A.charts; Submodule ℂ F := by
  letI := A.charts
  let V := LinearMap.range
    (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,F)
      (Subtype.val : S → B) x).toLinearMap
  refine { carrier := {v : F | v ∈ V}
           zero_mem' := V.zero_mem
           add_mem' := V.add_mem
           smul_mem' := ?_ }
  intro c v hv
  have hi : Complex.I • v ∈ V := hA x v hv
  rw [← Complex.re_add_im c]
  simp only [add_smul, mul_smul, Complex.coe_smul]
  exact V.add_mem (V.smul_mem c.re hv) (V.smul_mem c.im hi)

/-- The complex atlas supplied by the general criterion is smoothly
compatible with the actual original real atlas. The subset inclusion is
holomorphic for this atlas. No action or line bundle is part of the source. -/
structure CompatibleComplexAtlas {S : Set B} {k : ℕ}
    (A : RealEmbeddedAtlas (F := F) S k) (m : ℕ) where
  charts : ChartedSpace (EuclideanSpace ℂ (Fin m)) S
  manifold : letI := charts
    IsManifold 𝓘(ℂ,EuclideanSpace ℂ (Fin m)) ∞ S
  realManifold : letI := charts
    IsManifold 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) ∞ S
  smoothToReal : letI := A.charts
    letI := charts
    ContMDiff 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
      𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ (id : S → S)
  smoothFromReal : letI := A.charts
    letI := charts
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
      𝓘(ℝ,EuclideanSpace ℂ (Fin m)) ∞ (id : S → S)
  inclusion_holomorphic : letI := charts
    ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin m)) 𝓘(ℂ,F) ∞
      (Subtype.val : S → B)

/-- The compatible complex atlas preserves the immersion property of the
original real embedded atlas. This is the actual inclusion differential,
not a new embedding hypothesis. -/
theorem CompatibleComplexAtlas.inclusion_injective_derivative
    [IsManifold 𝓘(ℝ,F) ∞ B]
    {S : Set B} {k m : ℕ}
    (A : RealEmbeddedAtlas (F := F) S k)
    (C : CompatibleComplexAtlas A m) :
    letI := C.charts
    ∀ x : S, Function.Injective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) 𝓘(ℝ,F)
        (Subtype.val : S → B) x) := by
  letI := A.charts
  letI := A.manifold
  letI := C.charts
  letI := C.realManifold
  intro x u v huv
  have hTo := C.smoothToReal.mdifferentiableAt (by simp) (x := x)
  have hFrom := C.smoothFromReal.mdifferentiableAt (by simp) (x := x)
  have hA := A.inclusion_smooth.mdifferentiableAt (by simp) (x := x)
  have hchain : mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) 𝓘(ℝ,F)
      (Subtype.val : S → B) x =
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,F)
        (Subtype.val : S → B) x).comp
        (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
          𝓘(ℝ,EuclideanSpace ℝ (Fin k)) id x) := by
    simpa only [Function.comp_id, id_eq] using mfderiv_comp x hA hTo
  have hxy : mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
      𝓘(ℝ,EuclideanSpace ℝ (Fin k)) id x u =
      mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
        𝓘(ℝ,EuclideanSpace ℝ (Fin k)) id x v := by
    apply A.inclusion_injective_derivative x
    calc
      _ = mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m)) 𝓘(ℝ,F)
          (Subtype.val : S → B) x u := by
            exact (congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℝ] F => L u) hchain).symm
      _ = _ := huv
      _ = _ := by
        exact congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℝ] F => L v) hchain
  have hback := mfderiv_comp x hFrom hTo
  change mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
      𝓘(ℝ,EuclideanSpace ℂ (Fin m)) id x =
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
        𝓘(ℝ,EuclideanSpace ℂ (Fin m)) id x).comp
        (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
          𝓘(ℝ,EuclideanSpace ℝ (Fin k)) id x) at hback
  rw [mfderiv_id] at hback
  calc
    u = mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k))
        𝓘(ℝ,EuclideanSpace ℂ (Fin m)) id x
        (mfderiv 𝓘(ℝ,EuclideanSpace ℂ (Fin m))
          𝓘(ℝ,EuclideanSpace ℝ (Fin k)) id x u) := by
            simpa using (congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℝ]
              EuclideanSpace ℂ (Fin m) => L u) hback)
    _ = _ := by rw [hxy]
    _ = v := by
      simpa using congrArg (fun L : EuclideanSpace ℂ (Fin m) →L[ℝ]
        EuclideanSpace ℂ (Fin m) => L v) hback.symm

/-- The literal general criterion, restricted to finite-dimensional
Hausdorff second-countable manifolds. Applying it to a fixed set still
requires constructing the real atlas and verifying its actual tangent
condition. It does not assume a fixed-component complex atlas. -/
def ClosedComplexTangentSubmanifoldTheorem : Prop :=
  ∀ {F B : Type}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B] [IsManifold 𝓘(ℝ,F) ∞ B]
    (S : Set B) (_hClosed : IsClosed S) (k : ℕ)
    (A : RealEmbeddedAtlas (F := F) S k),
    A.ComplexTangent → ∃ m : ℕ, Nonempty (CompatibleComplexAtlas A m)

end
end QuaternionicSymmetry.ComplexSubmanifoldInput

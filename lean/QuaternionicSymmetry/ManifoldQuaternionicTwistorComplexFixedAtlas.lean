import QuaternionicSymmetry.ComplexSubmanifoldDimension
import QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedComponentBridge

/-! The genuine real fixed-component atlas of the lifted isometries has
complex tangent spaces in the actual compatible twistor complex atlas.
The atlas change is differentiated explicitly; no invariant metric in the
complex coordinates, and no pre-existing complex fixed atlas, is assumed. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorComplexFixedAtlas

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorIsometryDiffeomorph
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorFixedComponentBridge
open ManifoldQuaternionicIsometryTwistorComplex
open ManifoldRiemannianFixedComponentGenericInput
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev R := E × EuclideanSpace ℝ (Fin 2)

/-- The actual derivative of the atlas comparison, with inverse obtained
by differentiating the opposite identity map. -/
def atlasTangentEquiv {n : ℕ} (C : CompatibleComplexAtlas Q D n)
    (z : SphereBundleTotal Q) :
    letI := C.charts
    ComplexTwistorModel n ≃L[ℝ] R (E := E) := by
  letI := C.charts
  let T := mfderiv 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
    (id : SphereBundleTotal Q → SphereBundleTotal Q) z
  let U := mfderiv (J (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
    (id : SphereBundleTotal Q → SphereBundleTotal Q) z
  have hT := C.smoothToExisting.mdifferentiableAt (by simp) (x := z)
  have hU := C.smoothFromExisting.mdifferentiableAt (by simp) (x := z)
  refine { T with
    invFun := U
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := T.continuous
    continuous_invFun := U.continuous }
  · intro v
    have h := mfderiv_comp z hU hT
    change mfderiv 𝓘(ℝ,ComplexTwistorModel n)
      𝓘(ℝ,ComplexTwistorModel n) id z = U.comp T at h
    rw [mfderiv_id] at h
    exact (congrArg (fun L : ComplexTwistorModel n →L[ℝ]
      ComplexTwistorModel n => L v) h).symm
  · intro v
    have h := mfderiv_comp z hT hU
    change mfderiv (J (E := E)) (J (E := E)) id z = T.comp U at h
    rw [mfderiv_id] at h
    exact (congrArg (fun L : R (E := E) →L[ℝ] R (E := E) => L v) h).symm

variable {n : ℕ} (C : CompatibleComplexAtlas Q D n)
  (S : Subgroup (QuaternionicIsometries Q))
  {z : SphereBundleTotal Q} {k : ℕ}
  (A : FixedComponentAtlas (J (E := E)) (liftedSet Q S) z k)

/-- Chain rule for the actual inclusion, not an abstract tangent-space
identification. -/
theorem inclusionDerivative_transport
    (x : FixedComponent (J (E := E)) (liftedSet Q S) z)
    (v : EuclideanSpace ℝ (Fin k)) :
    letI := C.charts
    letI := A.charts
    atlasTangentEquiv Q D C x.1
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) 𝓘(ℝ,ComplexTwistorModel n)
        Subtype.val x v) =
    mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E))
      Subtype.val x v := by
  letI := C.charts
  letI := A.charts
  have hi := C.smoothFromExisting.comp A.inclusion_smooth
  have h := mfderiv_comp x
    (C.smoothToExisting.mdifferentiableAt (by simp) (x := x.1))
    (hi.mdifferentiableAt (by simp) (x := x))
  exact (congrArg (fun L : EuclideanSpace ℝ (Fin k) →L[ℝ]
    R (E := E) => L v) h).symm

/-- The same real fixed-component atlas, now embedded in the compatible
complex ambient atlas. Injectivity follows from the actual chain rule. -/
def realEmbeddedAtlas :
    letI := C.charts
    ComplexSubmanifoldInput.RealEmbeddedAtlas (F := ComplexTwistorModel n)
      (connectedComponentIn (fixedSpherePoints Q S) z) k := by
  letI := C.charts
  letI := A.charts
  letI : ChartedSpace (EuclideanSpace ℝ (Fin k))
      ↥(connectedComponentIn (fixedSpherePoints Q S) z) := A.charts
  refine {
    charts := A.charts
    manifold := A.manifold
    inclusion_smooth := C.smoothFromExisting.comp A.inclusion_smooth
    inclusion_injective_derivative := ?_ }
  letI := A.charts
  intro x u v huv
  apply A.inclusion_injective_derivative x
  have h := congrArg (atlasTangentEquiv Q D C x.1) huv
  exact (inclusionDerivative_transport Q D C S A x u).symm.trans
    (h.trans (inclusionDerivative_transport Q D C S A x v))

private theorem tangent_transport (a b : SphereBundleTotal Q) (h : a = b)
    (v : TangentSpace (J (E := E)) a) :
    (show R (E := E) from (h ▸ v : TangentSpace (J (E := E)) b)) =
      (show R (E := E) from v) := by
  cases h
  rfl

/-- The independently proved naturality of the full twistor derivative
makes its genuine common fixed tangent subspace almost-complex invariant. -/
theorem fixedVectors_tangentComplex
    (x : SphereBundleTotal Q) (hx : x ∈ fixedSpherePoints Q S)
    (v : TangentSpace (J (E := E)) x)
    (hv : v ∈ fixedVectors (J (E := E)) (liftedSet Q S) x hx) :
    tangentComplex Q D x v ∈
      fixedVectors (J (E := E)) (liftedSet Q S) x hx := by
  intro g hg
  obtain ⟨f,rfl⟩ := hg
  have hf := hx (realLift Q f.1) ⟨f,rfl⟩
  have hfv := (tangent_transport Q ((realLift Q f.1) x) x hf
    (mfderiv (J (E := E)) (J (E := E))
      (realLift Q f.1 : SphereBundleTotal Q → SphereBundleTotal Q) x v)).symm.trans
      (hv (realLift Q f.1) ⟨f,rfl⟩)
  apply (tangent_transport Q ((realLift Q f.1) x) x hf _).trans
  change mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f.1) x
    (tangentComplex Q D x v) = tangentComplex Q D x v
  rw [sphereTotalMap_mfderiv_intertwines_tangentComplex Q D f.1 x v]
  change sphereTotalMap Q f.1 x = x at hf
  change mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f.1) x v = v at hfv
  rw [hfv, hf]

/-- The actual inclusion's tangent range is complex in the compatible
atlas: transport to the real fixed-vector description and back. -/
theorem realEmbeddedAtlas_complexTangent :
    letI := C.charts
    (realEmbeddedAtlas Q D C S A).ComplexTangent := by
  letI := C.charts
  letI := A.charts
  letI : ChartedSpace (EuclideanSpace ℝ (Fin k))
      ↥(connectedComponentIn (fixedSpherePoints Q S) z) := A.charts
  intro x v hv
  let T := atlasTangentEquiv Q D C x.1
  have hTv : T v ∈ LinearMap.range
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E))
        Subtype.val x).toLinearMap := by
    obtain ⟨u,hu⟩ := hv
    refine ⟨u, ?_⟩
    exact (inclusionDerivative_transport Q D C S A x u).symm.trans (congrArg T hu)
  have hJ := fixedVectors_tangentComplex Q D S x.1
    (connectedComponentIn_subset _ _ x.2) (T v) ((A.tangent_eq x (T v)).mp hTv)
  obtain ⟨u,hu⟩ := (A.tangent_eq x (tangentComplex Q D x.1 (T v))).mpr hJ
  refine ⟨u, T.injective ?_⟩
  exact (inclusionDerivative_transport Q D C S A x u).trans
    (hu.trans (C.tangentI x.1 v).symm)

theorem fixedSpherePoints_isClosed [T2Space M] :
    IsClosed (fixedSpherePoints Q S) := by
  change IsClosed {x : SphereBundleTotal Q | ∀ f ∈ liftedSet Q S, f x = x}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_eq f.continuous continuous_id

theorem fixedSphereComponent_isClosed [T2Space M]
    (hz : z ∈ fixedSpherePoints Q S) :
    IsClosed (connectedComponentIn (fixedSpherePoints Q S) z) := by
  rw [connectedComponentIn_eq_image hz]
  exact (fixedSpherePoints_isClosed Q S).isClosedMap_subtype_val _
    isClosed_connectedComponent

/-- Apply only the general complex-submanifold criterion to the exact
real component selected by the Riemannian fixed-component theorem. -/
theorem exists_compatibleComplexAtlas [T2Space M] [CompactSpace M]
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (hz : z ∈ fixedSpherePoints Q S) :
    letI := C.charts
    ∃ m : ℕ, Nonempty
      (ComplexSubmanifoldInput.CompatibleComplexAtlas (realEmbeddedAtlas Q D C S A) m) := by
  letI := C.charts
  letI := C.complexManifold
  letI := C.realManifold
  exact hComplex _ (fixedSphereComponent_isClosed Q S hz) k
    (realEmbeddedAtlas Q D C S A) (realEmbeddedAtlas_complexTangent Q D C S A)

/-- The selected complex atlas has the correct dimension, obtained from
the differentiated atlas comparison rather than added to the source. -/
theorem exists_compatibleComplexAtlas_dimension [T2Space M] [CompactSpace M]
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (hz : z ∈ fixedSpherePoints Q S) :
    letI := C.charts
    ∃ m : ℕ, ∃ B : ComplexSubmanifoldInput.CompatibleComplexAtlas
      (realEmbeddedAtlas Q D C S A) m, k = 2 * m := by
  letI := C.charts
  obtain ⟨m,⟨B⟩⟩ := exists_compatibleComplexAtlas Q D C S A hComplex hz
  refine ⟨m,B,?_⟩
  exact B.real_dimension_eq_twice (realEmbeddedAtlas Q D C S A)
    ⟨z,mem_connectedComponentIn hz⟩

/-- Composition of the literal Riemannian fixed-component theorem and the
general complex-submanifold theorem. The metric argument is a construction
obligation, not an additional literature premise. -/
theorem exists_complexFixedAtlas_of_packaged_metric [T2Space M] [CompactSpace M]
    (hFixed : RiemannianFixedComponentOnModel
      (F := R (E := E)) (H := ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (N := SphereBundleTotal Q) (J (E := E)))
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (g : SmoothMetric (F := R (E := E))
      (N := SphereBundleTotal Q) (J (E := E)))
    (hg : ∀ x (u v : TangentSpace (J (E := E)) x),
      g.inner x u v = ManifoldQuaternionicTwistorSplitMetric.splitMetric Q D x u v)
    (hz : z ∈ fixedSpherePoints Q S) :
    letI := C.charts
    ∃ k : ℕ, ∃ A : FixedComponentAtlas (J (E := E)) (liftedSet Q S) z k,
      ∃ m : ℕ, ∃ B : ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas Q D C S A) m, k = 2 * m := by
  letI := C.charts
  obtain ⟨k,⟨A⟩⟩ :=
    exists_liftedFixedComponentAtlas_of_packaged_metric Q D hFixed g hg S z hz
  obtain ⟨m,B,hdim⟩ := exists_compatibleComplexAtlas_dimension Q D C S A hComplex hz
  exact ⟨k,A,m,B,hdim⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorComplexFixedAtlas

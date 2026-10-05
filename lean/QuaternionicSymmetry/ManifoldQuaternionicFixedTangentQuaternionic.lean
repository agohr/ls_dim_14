import QuaternionicSymmetry.ManifoldQuaternionicFixedComponentDimension
import QuaternionicSymmetry.ManifoldQuaternionicIsometryCoefficients
import QuaternionicSymmetry.QuaternionicRestriction
import QuaternionicSymmetry.QuaternionicAction

/-! If the actual isotropy acts trivially on the quaternionic three-plane,
its fixed tangent space is quaternionic. This is proved in an adapted
orthonormal frame and then transported to the actual tangent subspace;
no quaternionic dimension or divisibility is assumed. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFixedTangentQuaternionic

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFixedTangentDimension
open ManifoldQuaternionicDerivativeAction ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIntrinsicTwistorComparison
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (S : Subgroup (QuaternionicIsometries Q)) (x : M)
  (hx : x ∈ fixedPoints Q S)

theorem fixedTangentSpace_generator_mem
    (hQ : ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f x a = a)
    (t : Fin 3) {v : TangentSpace 𝓘(ℝ,E) x}
    (hv : v ∈ fixedTangentSpace Q S x hx) :
    tangentGenerator Q x t v ∈ fixedTangentSpace Q S x hx := by
  intro f hf
  have hconj : tangentConjugation Q f x (tangentGenerator Q x t) =
      tangentGenerator Q x t := by
    rw [← tangentSynth_basis Q x t, ← tangentSynth_coefficientAction,
      hx f hf, hQ f hf]
  have h := tangentConjugation_apply_tangentEquiv Q f x
    (tangentGenerator Q x t) v
  rw [hconj] at h
  change tangentGenerator Q x t
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (f.1 : M → M) x v) = _ at h
  rw [hv f hf] at h
  exact h.symm

/-- Pull the actual fixed tangent subspace back through its genuine
adapted orthonormal frame. -/
def adaptedFixedSpace : Submodule ℝ E :=
  (fixedTangentSpace Q S x hx).comap
    (Q.frames.fromFrame ((tangentBundleCore 𝓘(ℝ,E) M).indexAt x) x).toLinearMap

theorem adaptedFixedSpace_generator_mem
    (hQ : ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f x a = a)
    (t : Fin 3) {v : E} (hv : v ∈ adaptedFixedSpace Q S x hx) :
    VectorBundleFrameTransitions.quaternionicGenerator
      (Q.reduction.Q ((tangentBundleCore 𝓘(ℝ,E) M).indexAt x)) t v ∈
      adaptedFixedSpace Q S x hx := by
  let i := (tangentBundleCore 𝓘(ℝ,E) M).indexAt x
  have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x
  have h := fixedTangentSpace_generator_mem Q S x hx hQ t hv
  change (Q.frames.fromFrame i x)
    (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q i) t
      (Q.frames.toFrame i x (Q.frames.fromFrame i x v))) ∈ _ at h
  rw [Q.frames.to_from i x hi] at h
  exact h

/-- The restricted quaternionic structure on the actual invariant tangent
space expressed in an adapted orthonormal frame. -/
def fixedQuaternionicStructure
    (hQ : ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f x a = a) :
    QuaternionicStructure (adaptedFixedSpace Q S x hx) :=
  (Q.reduction.Q ((tangentBundleCore 𝓘(ℝ,E) M).indexAt x)).restrict
    (adaptedFixedSpace Q S x hx)
    (fun {_} hv => adaptedFixedSpace_generator_mem Q S x hx hQ 0 hv)
    (fun {_} hv => adaptedFixedSpace_generator_mem Q S x hx hQ 1 hv)

/-- Returning from the orthonormal frame identifies this quaternionic
subspace with the genuine fixed vectors in the tangent fiber. -/
def adaptedFixedEquiv : adaptedFixedSpace Q S x hx ≃ₗ[ℝ]
    fixedTangentSpace Q S x hx where
  toFun v := ⟨Q.frames.fromFrame ((tangentBundleCore 𝓘(ℝ,E) M).indexAt x) x v,
    v.2⟩
  invFun v := ⟨Q.frames.toFrame ((tangentBundleCore 𝓘(ℝ,E) M).indexAt x) x
    (show E from v.1), by
    change Q.frames.fromFrame ((tangentBundleCore 𝓘(ℝ,E) M).indexAt x) x
      (Q.frames.toFrame ((tangentBundleCore 𝓘(ℝ,E) M).indexAt x) x
        (show E from v.1)) ∈ (show Submodule ℝ E from fixedTangentSpace Q S x hx)
    rw [Q.frames.from_to _ x ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x)]
    exact v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact Q.frames.to_from _ x ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x) v
  right_inv v := by
    apply Subtype.ext
    exact Q.frames.from_to _ x ((tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at x)
      (show E from v.1)
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c v := by apply Subtype.ext; exact map_smul _ _ _

theorem four_dvd_fixedTangent_finrank
    (hQ : ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f x a = a) :
    4 ∣ Module.finrank ℝ (fixedTangentSpace Q S x hx) := by
  rw [← (adaptedFixedEquiv Q S x hx).finrank_eq]
  exact (fixedQuaternionicStructure Q S x hx hQ).four_dvd_real_finrank

include hx in
/-- Quaternionic divisibility for the dimension of an actual fixed
component follows already from trivial quaternionic isotropy at one of
its points. Extending that triviality along the component is needed for
its global induced quaternionic geometry, not for this dimension fact. -/
theorem four_dvd_fixedComponent_dimension {k : ℕ}
    (C : ManifoldRiemannianFixedComponentInput.FixedComponentAtlas Q S x k)
    (hQ : ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f x a = a) :
    4 ∣ k := by
  let y : ManifoldRiemannianFixedComponentInput.FixedComponent Q S x :=
    ⟨x, mem_connectedComponentIn hx⟩
  rw [ManifoldQuaternionicFixedComponentDimension.atlas_dimension_eq_fixedTangent_finrank
    Q S x C y]
  exact four_dvd_fixedTangent_finrank Q S x hx hQ

include hx in
/-- The actual fixed-component atlas can be indexed by a strictly smaller
quaternionic dimension. Positive dimension and induced positive curvature
are separate obligations. -/
theorem exists_smaller_quaternionic_fixedComponent [T2Space M]
    [SecondCountableTopology M] [PreconnectedSpace M]
    (hjet : ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel
      (E := E) (M := M))
    (hfixed : ManifoldRiemannianFixedComponentInput.RiemannianFixedComponentOnModel
      (E := E) (M := M))
    (hS : ∃ f ∈ S, f ≠ 1)
    (hQ : ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f x a = a)
    (R : QuaternionicStructure E) :
    ∃ m : ℕ, m < R.quaternionicDimension ∧
      Nonempty (ManifoldRiemannianFixedComponentInput.FixedComponentAtlas
        Q S x (4*m)) := by
  obtain ⟨k, hk, ⟨C⟩⟩ :=
    ManifoldQuaternionicFixedComponentDimension.exists_fixedComponentAtlas_dimension_lt
      Q hjet hfixed S hS x hx
  obtain ⟨m, hm⟩ := four_dvd_fixedComponent_dimension Q S x hx C hQ
  refine ⟨m, ?_, ?_⟩
  · have hdim := R.real_finrank
    omega
  · rw [← hm]
    exact ⟨C⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedTangentQuaternionic

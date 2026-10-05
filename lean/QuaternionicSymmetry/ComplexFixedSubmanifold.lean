import QuaternionicSymmetry.ComplexSubmanifoldInput
import QuaternionicSymmetry.ManifoldRiemannianFixedComponentGenericInput

/-! The complex-tangent step for genuine fixed components. The real atlas
and its exact tangent description come from general Riemannian fixed-set
geometry; complex linearity of the actual action derivatives is verified
separately. The general complex-submanifold criterion is the only complex
atlas input, not an assumption of a complex fixed-component atlas. -/

namespace QuaternionicSymmetry.ComplexFixedSubmanifold

open ManifoldRiemannianFixedComponentGenericInput
open ComplexSubmanifoldInput
open scoped Manifold ContDiff
noncomputable section

variable {F B : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] [Nontrivial F]
  [TopologicalSpace B] [ChartedSpace F B]
  [IsManifold 𝓘(ℝ,F) ∞ B]
variable (S : Set (Diffeomorph 𝓘(ℝ,F) 𝓘(ℝ,F) B B ∞))

private theorem tangent_transport (a b : B) (h : a = b)
    (v : TangentSpace 𝓘(ℝ,F) a) :
    (show F from (h ▸ v : TangentSpace 𝓘(ℝ,F) b)) = (show F from v) := by
  cases h
  rfl

/-- Retain the exact subset, atlas and inclusion supplied by BG-R2. -/
def realEmbeddedAtlas {x : B} {k : ℕ}
    (A : FixedComponentAtlas 𝓘(ℝ,F) S x k) :
    RealEmbeddedAtlas (F := F)
      (connectedComponentIn (fixedPoints 𝓘(ℝ,F) S) x) k where
  charts := A.charts
  manifold := A.manifold
  inclusion_smooth := A.inclusion_smooth
  inclusion_injective_derivative := A.inclusion_injective_derivative

/-- Actual derivative-fixed vectors remain fixed after multiplication by
`i` whenever the genuine action derivatives commute with `i`. -/
theorem fixedVectors_smul_i
    (hI : ∀ f ∈ S, ∀ x : B, ∀ v : F,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) x (Complex.I • v) =
        Complex.I • (show F from mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) x v))
    (x : B) (hx : x ∈ fixedPoints 𝓘(ℝ,F) S)
    (v : F) (hv : v ∈ fixedVectors 𝓘(ℝ,F) S x hx) :
    Complex.I • v ∈ fixedVectors 𝓘(ℝ,F) S x hx := by
  intro f hf
  have hfv := hv f hf
  have hfv' := (tangent_transport (f x) x (hx f hf)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) x v)).symm.trans hfv
  exact (tangent_transport (f x) x (hx f hf)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) x (Complex.I • v))).trans
      ((hI f hf x v).trans (congrArg (fun w : F => Complex.I • w) hfv'))

/-- The exact tangent identification of BG-R2, together with actual
complex-linearity of the action differential, proves the criterion's
tangent hypothesis for the real fixed-component atlas. -/
theorem realEmbeddedAtlas_complexTangent
    {x : B} {k : ℕ} (A : FixedComponentAtlas 𝓘(ℝ,F) S x k)
    (hI : ∀ f ∈ S, ∀ y : B, ∀ v : F,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) y (Complex.I • v) =
        Complex.I • (show F from mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) y v)) :
    (realEmbeddedAtlas S A).ComplexTangent := by
  letI := A.charts
  intro y v hv
  apply (A.tangent_eq y (Complex.I • (show F from v))).mpr
  exact fixedVectors_smul_i S hI y.1
    (connectedComponentIn_subset _ _ y.2) v ((A.tangent_eq y v).mp hv)

theorem fixedPoints_isClosed [T2Space B] :
    IsClosed (fixedPoints 𝓘(ℝ,F) S) := by
  change IsClosed {x : B | ∀ f ∈ S, f x = x}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_eq f.continuous continuous_id

theorem fixedComponent_isClosed [T2Space B]
    (x : B) (hx : x ∈ fixedPoints 𝓘(ℝ,F) S) :
    IsClosed (connectedComponentIn (fixedPoints 𝓘(ℝ,F) S) x) := by
  rw [connectedComponentIn_eq_image hx]
  exact (fixedPoints_isClosed S).isClosedMap_subtype_val _
    isClosed_connectedComponent

/-- The literal general complex-submanifold criterion now applies to the
genuine fixed component. Every fixed-specific geometric premise has been
reduced to its real atlas and the actual derivative calculation above. -/
theorem exists_compatibleComplexAtlas
    [T2Space B] [SecondCountableTopology B]
    [IsManifold 𝓘(ℂ,F) ∞ B]
    (hComplex : ClosedComplexTangentSubmanifoldTheorem)
    {x : B} (hx : x ∈ fixedPoints 𝓘(ℝ,F) S) {k : ℕ}
    (A : FixedComponentAtlas 𝓘(ℝ,F) S x k)
    (hI : ∀ f ∈ S, ∀ y : B, ∀ v : F,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) y (Complex.I • v) =
        Complex.I • (show F from mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) y v)) :
    ∃ m : ℕ, Nonempty (CompatibleComplexAtlas (realEmbeddedAtlas S A) m) := by
  exact hComplex _ (fixedComponent_isClosed S x hx) k
    (realEmbeddedAtlas S A) (realEmbeddedAtlas_complexTangent S A hI)

/-- Applying the two literal general sources leaves no assumed real or
complex fixed-component atlas. The metric and its preservation are genuine
geometric data, and the complex tangent condition is proved above. -/
theorem exists_complexFixedAtlas_from_metric
    [T2Space B] [SecondCountableTopology B]
    [IsManifold 𝓘(ℂ,F) ∞ B]
    (hFixed : RiemannianFixedComponentOnModel (N := B) 𝓘(ℝ,F))
    (hComplex : ClosedComplexTangentSubmanifoldTheorem)
    (g : SmoothMetric (N := B) 𝓘(ℝ,F))
    (hPres : ∀ f ∈ S, PreservesMetric 𝓘(ℝ,F) g f)
    (hI : ∀ f ∈ S, ∀ y : B, ∀ v : F,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) y (Complex.I • v) =
        Complex.I • (show F from mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) (f : B → B) y v))
    (x : B) (hx : x ∈ fixedPoints 𝓘(ℝ,F) S) :
    ∃ k : ℕ, ∃ A : FixedComponentAtlas 𝓘(ℝ,F) S x k,
      ∃ m : ℕ, Nonempty (CompatibleComplexAtlas (realEmbeddedAtlas S A) m) := by
  obtain ⟨k, ⟨A⟩⟩ := hFixed g S hPres x hx
  exact ⟨k, A, exists_compatibleComplexAtlas S hComplex hx A hI⟩

end
end QuaternionicSymmetry.ComplexFixedSubmanifold

import QuaternionicSymmetry.HolomorphicTangentSectionCoordinates
import QuaternionicSymmetry.ContactHamiltonianLocalUniqueness

/-! Contraction is a bijection from genuine holomorphic contact vector
fields to holomorphic sections of the contact line. Contact fields are
defined by Lie brackets preserving the actual local contact kernels. -/
namespace QuaternionicSymmetry.HolomorphicContactHamiltonianBijection
open HolomorphicLineOneFormCoordinates HolomorphicLineSectionCoordinates
open HolomorphicContactHamiltonianCoordinates HolomorphicContactHamiltonianField
open HolomorphicTangentSectionCoordinates ContactExteriorDerivativeCalculus
open ContactDeterminantAlgebra ContactHamiltonianLocalSmooth Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ,V) ∞ M]
  {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (θ : ∀ x : M, TangentSpace 𝓘(ℂ,V) x →ₗ[ℂ] L.Fiber x)
local notation "S" => ContMDiffSection 𝓘(ℂ,V) V ∞ (TangentSpace 𝓘(ℂ,V) : M → Type _)
local notation "H" => ContMDiffSection 𝓘(ℂ,V) ℂ ∞ L.Fiber

/-- The local bracket definition of preservation of the contact hyperplane. -/
def IsContact (X : S) : Prop :=
  ∀ (i : atlas V M) (a : ι) (x : M), x ∈ i.1.source → x ∈ L.baseSet a →
    ∀ Y : V → V, DifferentiableAt ℂ Y (i.1 x) →
      ((fun y => coordinateForm L θ i a y (Y y)) =ᶠ[𝓝 (i.1 x)] fun _ => 0) →
      coordinateForm L θ i a (i.1 x)
        (VectorField.lieBracket ℂ (coordinateField X i) Y (i.1 x)) = 0

variable (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
    (fun t : TangentBundle 𝓘(ℂ,V) M => (⟨t.1,θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))
  (hN : ∀ (i : atlas V M) (a : ι) (x : M), x ∈ i.1.source → x ∈ L.baseSet a →
    (border (coordinateForm L θ i a (i.1 x)).toLinearMap
      (exteriorDerivative (coordinateForm L θ i a) (i.1 x))).Nondegenerate)

def contractionSection (X : S) : H := ⟨fun x => θ x (X x),hθ.comp X.contMDiff⟩

theorem coordinate_value (X : S) (s : H) (he : ∀ x, θ x (X x) = s x)
    (i : atlas V M) (a : ι) (x : M) (hi : x ∈ i.1.source) :
    (fun y => coordinateForm L θ i a y (coordinateField X i y)) =ᶠ[𝓝 (i.1 x)]
      coordinateSection L s i a := by
  filter_upwards [i.1.open_target.mem_nhds (i.1.map_source hi)] with y hy
  rw [coordinate_contraction L θ X i a y hy]
  unfold coordinateSection localSection
  dsimp only
  rw [he]

/-- The constructed Hamiltonian preserves the contact distribution. -/
theorem hamiltonian_isContact (s : H) :
    IsContact L θ (tangentSection L θ hθ s s.contMDiff hN) := by
  intro i a x hi ha Y hY hYker
  let X := tangentSection L θ hθ s s.contMDiff hN
  have hvalue := coordinate_value L θ X s (contraction L θ hθ s s.contMDiff hN) i a x hi
  have hcoord := coordinateField_hamiltonian L θ hθ s s.contMDiff hN i a (i.1 x)
    ⟨i.1.map_source hi,by simpa [i.1.left_inv hi] using ha⟩
  apply ContactHamiltonianLocalCovariance.lieBracket_horizontal
    (coordinateForm L θ i a) (coordinateSection L s i a) (coordinateField X i) Y
    (localSolution (coordinateForm L θ i a) (coordinateSection L s i a) (i.1 x)).2 (i.1 x)
    ((coordinateForm_contDiffAt L θ hθ i a x hi ha).differentiableAt (by simp))
    ((coordinateSection_contDiffAt L s s.contMDiff i a x hi ha).differentiableAt (by simp))
    ((coordinateField_contDiffAt X i x hi).differentiableAt (by simp)) hY hvalue
  · intro v
    rw [hcoord]
    exact localSolution_levi (coordinateForm L θ i a) (coordinateSection L s i a) (i.1 x)
      v (hN i a x hi ha)
  · exact hYker

/-- Uniqueness for the actual globally glued Hamiltonian section. -/
theorem eq_hamiltonian (X : S) (hX : IsContact L θ X) (s : H)
    (he : ∀ x, θ x (X x) = s x) : X = tangentSection L θ hθ s s.contMDiff hN := by
  apply ContMDiffSection.ext
  intro x
  let i := achart V x
  let a := L.indexAt x
  have hi : x ∈ i.1.source := mem_chart_source V x
  have ha : x ∈ L.baseSet a := L.mem_baseSet_at x
  have hh := ContactHamiltonianLocalUniqueness.eq_localSolution
    (coordinateForm L θ i a) (coordinateSection L s i a) (coordinateField X i) (i.1 x)
    ((coordinateForm_contDiffAt L θ hθ i a x hi ha).differentiableAt (by simp))
    ((coordinateField_contDiffAt X i x hi).differentiableAt (by simp))
    (coordinate_value L θ X s he i a x hi) (hN i a x hi ha) (hX i a x hi ha)
  have hc : coordinateField X i (i.1 x) = X x := coordinateField_center X x
  rw [hc] at hh
  exact hh

include hN in
theorem contraction_bijective : Function.Bijective
    (fun X : {X : S // IsContact L θ X} => contractionSection L θ hθ X.1) := by
  constructor
  · intro X Y h
    change contractionSection L θ hθ X.1 = contractionSection L θ hθ Y.1 at h
    apply Subtype.ext
    calc
      X.1 = tangentSection L θ hθ (contractionSection L θ hθ X.1)
          (contractionSection L θ hθ X.1).contMDiff hN :=
        eq_hamiltonian L θ hθ hN X.1 X.2 _ (fun _ => rfl)
      _ = tangentSection L θ hθ (contractionSection L θ hθ Y.1)
          (contractionSection L θ hθ Y.1).contMDiff hN := by rw [h]
      _ = Y.1 := (eq_hamiltonian L θ hθ hN Y.1 Y.2 _ (fun _ => rfl)).symm
  · intro s
    refine ⟨⟨tangentSection L θ hθ s s.contMDiff hN,hamiltonian_isContact L θ hθ hN s⟩,?_⟩
    apply ContMDiffSection.ext
    exact contraction L θ hθ s s.contMDiff hN

end
end QuaternionicSymmetry.HolomorphicContactHamiltonianBijection

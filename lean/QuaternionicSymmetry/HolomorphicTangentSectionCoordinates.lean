import QuaternionicSymmetry.HolomorphicContactHamiltonianField

/-! Coordinates of genuine holomorphic tangent sections and their
contraction with the contact form. -/
namespace QuaternionicSymmetry.HolomorphicTangentSectionCoordinates
open HolomorphicLineOneFormCoordinates HolomorphicLineSectionCoordinates
open HolomorphicContactHamiltonianCoordinates HolomorphicContactHamiltonianField
open Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℂ,V) ∞ M]
local notation "T" => tangentBundleCore 𝓘(ℂ,V) M
local notation "S" => ContMDiffSection 𝓘(ℂ,V) V ∞ (TangentSpace 𝓘(ℂ,V) : M → Type _)

def coordinateField (X : S) (i : atlas V M) (y : V) : V :=
  (T).coordChange (achart V (i.1.symm y)) i (i.1.symm y) (X (i.1.symm y))

theorem coordinateField_contDiffAt (X : S) (i : atlas V M) (x : M)
    (hi : x ∈ i.1.source) : ContDiffAt ℂ ∞ (coordinateField X i) (i.1 x) := by
  letI : IsManifold 𝓘(ℂ,V) (∞+1) M := by simpa using (inferInstance : IsManifold 𝓘(ℂ,V) ∞ M)
  letI : (T).IsContMDiff 𝓘(ℂ,V) ∞ := tangentBundleCore.isContMDiff
  letI : MemTrivializationAtlas ((T).localTriv i) := ⟨⟨i,rfl⟩⟩
  have h := (((T).localTriv i).contMDiffAt_section_iff hi).1 (X.contMDiff x)
  have hinv := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ,V)) (n := ∞)
    (IsManifold.subset_maximalAtlas i.2) (i.1.map_source hi)
  exact contMDiffAt_iff_contDiffAt.mp (h.comp_of_eq hinv (i.1.left_inv hi))

theorem coordinateField_center (X : S) (x : M) :
    coordinateField X (achart V x) ((chartAt V x) x) = X x := by
  change (T).coordChange (achart V ((chartAt V x).symm ((chartAt V x) x))) (achart V x)
    ((chartAt V x).symm ((chartAt V x) x)) (X ((chartAt V x).symm ((chartAt V x) x))) = _
  rw [(chartAt V x).left_inv (mem_chart_source V x)]
  exact (T).coordChange_self (achart V x) x (mem_chart_source V x) (X x)

variable {ι : Type*} (L : VectorBundleCore ℂ M ℂ ι) [L.IsContMDiff 𝓘(ℂ,V) ∞]
  (θ : ∀ x : M, TangentSpace 𝓘(ℂ,V) x →ₗ[ℂ] L.Fiber x)

theorem coordinate_contraction (X : S) (i : atlas V M) (a : ι) (y : V)
    (hy : y ∈ i.1.target) :
    coordinateForm L θ i a y (coordinateField X i y) =
      coordinateSection L (fun x => θ x (X x)) i a y := by
  change L.coordChange (L.indexAt (i.1.symm y)) a (i.1.symm y)
    (θ (i.1.symm y) ((T).coordChange i (achart V (i.1.symm y)) (i.1.symm y)
      ((T).coordChange (achart V (i.1.symm y)) i (i.1.symm y) (X (i.1.symm y))))) = _
  rw [(T).coordChange_comp (achart V (i.1.symm y)) i (achart V (i.1.symm y))
    (i.1.symm y) ⟨⟨mem_chart_source V _,i.1.map_target hy⟩,mem_chart_source V _⟩,
    (T).coordChange_self (achart V (i.1.symm y)) (i.1.symm y) (mem_chart_source V _)]
  rfl

variable (hθ : ContMDiff (𝓘(ℂ,V)).tangent ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
    (fun t : TangentBundle 𝓘(ℂ,V) M => (⟨t.1,θ t.1 t.2⟩ : Bundle.TotalSpace ℂ L.Fiber)))
  (s : ∀ x, L.Fiber x)
  (hs : ContMDiff 𝓘(ℂ,V) ((𝓘(ℂ,V)).prod 𝓘(ℂ,ℂ)) ∞
    (fun x => (⟨x,s x⟩ : Bundle.TotalSpace ℂ L.Fiber)))
  (hN : ∀ (i : atlas V M) (a : ι) (x : M), x ∈ i.1.source → x ∈ L.baseSet a →
    (ContactDeterminantAlgebra.border (coordinateForm L θ i a (i.1 x)).toLinearMap
      (ContactExteriorDerivativeCalculus.exteriorDerivative (coordinateForm L θ i a) (i.1 x))).Nondegenerate)

theorem coordinateField_hamiltonian (i : atlas V M) (a : ι) (y : V)
    (hy : y ∈ coordinateDomain L i a) :
    coordinateField (tangentSection L θ hθ s hs hN) i y = coordinateHamiltonian L θ s i a y := by
  change (T).coordChange (achart V (i.1.symm y)) i (i.1.symm y) (field L θ s (i.1.symm y)) = _
  rw [field_eq_local L θ hθ s hs hN i a (i.1.symm y) (i.1.map_target hy.1) hy.2,
    (T).coordChange_comp i (achart V (i.1.symm y)) i (i.1.symm y)
      ⟨⟨i.1.map_target hy.1,mem_chart_source V _⟩,i.1.map_target hy.1⟩,
    (T).coordChange_self i (i.1.symm y) (i.1.map_target hy.1),i.1.right_inv hy.1]

end
end QuaternionicSymmetry.HolomorphicTangentSectionCoordinates

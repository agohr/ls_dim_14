import QuaternionicSymmetry.ManifoldTwistorLinearSystem

/-! Chartwise holomorphic coefficient sections and smooth maps into the
actual holomorphic line-bundle total space express the same condition. -/
namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore ManifoldQuaternionicMetric
  ManifoldQuaternionicConnection TopologicalSpace
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A) (r : ℤ)

theorem coefficientPrelocal_iff_holomorphicSection
    {U : Opens (SphereBundleTotal Q)}
    (f : ∀ x : U, (L.integerTwistCore Q D r).Fiber x) :
    letI := A.charts
    (coefficientPrelocal Q D L r).pred f ↔
      (holomorphicSectionPrelocal Q D L r).pred f := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D r
  let Z := L.integerTwistCore Q D r
  letI (i : L.Index) : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
  change (∀ i : L.Index,
    ContMDiffOn 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ,ℂ) ∞
      (twistCoefficient Q D L r i f) {x : U | x.1 ∈ Z.baseSet i}) ↔
    ContMDiff 𝓘(ℂ, ComplexTwistorModel n)
      (𝓘(ℂ, ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)) ∞
      (fun x : U => (⟨x.1, f x⟩ : Bundle.TotalSpace ℂ Z.Fiber))
  constructor
  · intro hf x
    let i := Z.indexAt x.1
    have hx : x.1 ∈ Z.baseSet i := Z.mem_baseSet_at x.1
    have hcoeff := (hf i x hx).contMDiffAt
      ((Z.isOpen_baseSet i).preimage continuous_subtype_val |>.mem_nhds hx)
    have hsource : (⟨x.1, f x⟩ : Bundle.TotalSpace ℂ Z.Fiber) ∈
        (Z.localTriv i).source := (Z.mem_localTriv_source i _).mpr hx
    apply ((Z.localTriv i).contMDiffAt_iff
      (f := fun z : U => (⟨z.1, f z⟩ : Bundle.TotalSpace ℂ Z.Fiber)) hsource).mpr
    exact ⟨contMDiff_subtype_val.contMDiffAt, hcoeff⟩
  · intro hf i x hx
    have hsource : (⟨x.1, f x⟩ : Bundle.TotalSpace ℂ Z.Fiber) ∈
        (Z.localTriv i).source := (Z.mem_localTriv_source i _).mpr hx
    have h := ((Z.localTriv i).contMDiffAt_iff
      (f := fun z : U => (⟨z.1, f z⟩ : Bundle.TotalSpace ℂ Z.Fiber)) hsource).mp (hf x)
    exact h.2.contMDiffWithinAt

theorem global_coefficient_holomorphic_iff
    (f : ∀ x : SphereBundleTotal Q, (L.integerTwistCore Q D r).Fiber x) :
    letI := A.charts
    letI := L.integerTwistCore_holomorphic Q D r
    (fun x : (⊤ : Opens (SphereBundleTotal Q)) => f x.1) ∈
        coefficientSectionSubmodule Q D L r ⊤ ↔
      ContMDiff 𝓘(ℂ, ComplexTwistorModel n)
        (𝓘(ℂ, ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)) ∞
        (fun x => (⟨x, f x⟩ : Bundle.TotalSpace ℂ (L.integerTwistCore Q D r).Fiber)) := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D r
  change (coefficientPrelocal Q D L r).sheafify.pred
      (fun x : (⊤ : Opens (SphereBundleTotal Q)) => f x.1) ↔ _
  constructor
  · intro hf x
    obtain ⟨V, hx, i, hV⟩ := hf ⟨x, Set.mem_univ x⟩
    have htotal := (coefficientPrelocal_iff_holomorphicSection Q D L r _).mp hV
    have hlocal := htotal ⟨x, hx⟩
    change ContMDiffAt 𝓘(ℂ, ComplexTwistorModel n)
      (𝓘(ℂ, ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)) ∞
      (fun z : V => (⟨z.1, f z.1⟩ : Bundle.TotalSpace ℂ
        (L.integerTwistCore Q D r).Fiber)) ⟨x, hx⟩ at hlocal
    exact (contMDiffAt_subtype_iff (f := fun z =>
      (⟨z, f z⟩ : Bundle.TotalSpace ℂ (L.integerTwistCore Q D r).Fiber))).mp hlocal
  · intro hf
    apply TopCat.PrelocalPredicate.sheafifyOf
    apply (coefficientPrelocal_iff_holomorphicSection Q D L r _).mpr
    exact hf.comp contMDiff_subtype_val

/-- The two independently constructed global holomorphic-section spaces
are naturally complex-linearly equivalent, by their actual pointwise values. -/
def globalCoefficientSectionsEquiv :
    letI := A.charts
    letI := L.integerTwistCore_holomorphic Q D r
    ManifoldTwistorLinearSystem.GlobalSections Q D L r ≃ₗ[ℂ]
      HolomorphicTwistSections Q D L r := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D r
  refine {
    toFun := fun s => ⟨fun x => s.1 ⟨x, Set.mem_univ x⟩,
      (global_coefficient_holomorphic_iff Q D L r _).mp s.2⟩
    invFun := fun s => ⟨fun x => s x.1,
      (global_coefficient_holomorphic_iff Q D L r _).mpr s.contMDiff⟩
    left_inv := by
      intro s
      apply Subtype.ext
      rfl
    right_inv := by
      intro s
      apply ContMDiffSection.ext
      intro x
      rfl
    map_add' := by
      intro s t
      apply ContMDiffSection.ext
      intro x
      rfl
    map_smul' := by
      intro c s
      apply ContMDiffSection.ext
      intro x
      rfl }

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

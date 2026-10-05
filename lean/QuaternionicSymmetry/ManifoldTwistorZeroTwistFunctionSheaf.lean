import QuaternionicSymmetry.ManifoldTwistorZeroTwistSections
import QuaternionicSymmetry.HolomorphicUnitSheaf
import QuaternionicSymmetry.ComplexAbelianSheafAdjunction

/-! The zeroth contact twist is the actual holomorphic-function sheaf,
on every open set and compatibly with restriction. This comparison does
not infer a sheaf isomorphism merely from agreement of global sections. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open ManifoldTwistorSphereCore ManifoldQuaternionicMetric
  ManifoldQuaternionicConnection CategoryTheory TopologicalSpace Manifold
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A)

theorem zeroTwistPrelocal_iff {U : Opens (SphereBundleTotal Q)}
    (f : ∀ x : U, (L.integerTwistCore Q D 0).Fiber x) :
    letI := A.charts
    (coefficientPrelocal Q D L 0).pred f ↔
      ContMDiff 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ,ℂ) ∞ (fun x => (f x : ℂ)) := by
  letI := A.charts
  change (∀ i : L.Index,
    ContMDiffOn 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ,ℂ) ∞
      (twistCoefficient Q D L 0 i f)
      {x : U | x.1 ∈ (L.integerTwistCore Q D 0).baseSet i}) ↔ _
  constructor
  · intro hf x
    let Z := L.integerTwistCore Q D 0
    let i := Z.indexAt x.1
    have hx := Z.mem_baseSet_at x.1
    have h := (hf i x hx).contMDiffAt
      ((Z.isOpen_baseSet i).preimage continuous_subtype_val |>.mem_nhds hx)
    have heq : twistCoefficient Q D L 0 i f = fun x => (f x : ℂ) := by
      funext x
      exact zeroTwist_coordChange Q D L _ _ _ _
    rwa [heq] at h
  · intro hf i
    have heq : twistCoefficient Q D L 0 i f = fun x => (f x : ℂ) := by
      funext x
      exact zeroTwist_coordChange Q D L _ _ _ _
    rw [heq]
    exact hf.contMDiffOn

theorem zeroTwistSheafified_iff {U : Opens (SphereBundleTotal Q)}
    (f : ∀ x : U, (L.integerTwistCore Q D 0).Fiber x) :
    letI := A.charts
    (coefficientPrelocal Q D L 0).sheafify.pred f ↔
      ContMDiff 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ,ℂ) ∞ (fun x => (f x : ℂ)) := by
  letI := A.charts
  constructor
  · intro hf
    let P := (contDiffWithinAt_localInvariantProp
      (I := 𝓘(ℂ, ComplexTwistorModel n)) (I' := 𝓘(ℂ,ℂ)) ∞).localPredicate
        (SphereBundleTotal Q) ℂ
    change P.pred (fun x => (f x : ℂ))
    apply P.locality
    intro x
    obtain ⟨V, hx, j, hV⟩ := hf x
    exact ⟨V, hx, j, (zeroTwistPrelocal_iff Q D L _).mp hV⟩
  · intro hf
    apply TopCat.PrelocalPredicate.sheafifyOf
    exact (zeroTwistPrelocal_iff Q D L f).mpr hf

def zeroTwistFunctionSectionEquiv (U : Opens (SphereBundleTotal Q)) :
    letI := A.charts
    coefficientSectionSubmodule Q D L 0 U ≃+
      HolomorphicLineModuleSheaf.Functions 𝓘(ℂ, ComplexTwistorModel n) U := by
  letI := A.charts
  refine {
    toFun := fun s => ⟨fun x => (s.1 x : ℂ),
      (zeroTwistSheafified_iff Q D L s.1).mp s.2⟩
    invFun := fun f => ⟨fun x => f x,
      (zeroTwistSheafified_iff Q D L _).mpr f.contMDiff⟩
    left_inv := by intro s; apply Subtype.ext; rfl
    right_inv := by intro f; apply ContMDiffMap.ext; intro x; rfl
    map_add' := by intro f g; apply ContMDiffMap.ext; intro x; rfl }

def zeroTwistFunctionSheafIso :
    letI := A.charts
    (ComplexAbelianSheafAdjunction.forget (TopCat.of (SphereBundleTotal Q))).obj
        (holomorphicSectionComplexSheaf Q D L 0) ≅
      HolomorphicUnitSheaf.functionSheaf
        (B := SphereBundleTotal Q) 𝓘(ℂ, ComplexTwistorModel n) := by
  letI := A.charts
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  exact NatIso.ofComponents
    (fun U => (zeroTwistFunctionSectionEquiv Q D L U.unop).toAddCommGrpIso)
    (fun j => by ext s; rfl)

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

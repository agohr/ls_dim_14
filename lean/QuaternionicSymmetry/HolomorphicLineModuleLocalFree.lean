import QuaternionicSymmetry.HolomorphicLineModuleSheaf
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! On every open subset of an actual line chart, the genuine holomorphic
section module is free of rank one over the holomorphic function ring.
Both directions use the actual bundle-coordinate changes. This is local
freeness of represented bundle sections, not yet reconstruction of every
invertible analytic sheaf. -/

namespace QuaternionicSymmetry.HolomorphicLineModuleLocalFree

open CategoryTheory TopologicalSpace Manifold
open HolomorphicLineModuleSheaf
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F ι : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H) (Z : VectorBundleCore ℂ B ℂ ι)
  [Z.IsContMDiff IB ∞]

omit [Z.IsContMDiff IB ∞] in
theorem coefficient_holomorphic_of_le
    (i : ι) (U : Opens B) (hU : (U : Set B) ⊆ Z.baseSet i)
    (s : sectionSubmodule IB Z U) :
    ContMDiff IB 𝓘(ℂ,ℂ) ∞ (coefficient Z i s.1) := by
  let P := (contDiffWithinAt_localInvariantProp
    (I := IB) (I' := 𝓘(ℂ,ℂ)) ∞).localPredicate B ℂ
  apply P.locality
  intro x
  obtain ⟨V, hxV, j, hV⟩ := s.property x
  refine ⟨V, hxV, j, ?_⟩
  change ContMDiff IB 𝓘(ℂ,ℂ) ∞
    (fun y : V => coefficient Z i s.1 ⟨y.1, j.le y.2⟩)
  have hAll : {y : V | y.1 ∈ Z.baseSet i} = Set.univ :=
    Set.eq_univ_of_forall (fun y => hU (j.le y.2))
  have h := hV i
  rw [hAll, contMDiffOn_univ] at h
  exact h

/-- The local section with a prescribed holomorphic coordinate in the
actual `i`-th line chart. -/
def sectionOfFunction (i : ι) (U : Opens B)
    (hU : (U : Set B) ⊆ Z.baseSet i) (f : Functions IB U) :
    sectionSubmodule IB Z U := by
  refine ⟨fun x => Z.coordChange i (Z.indexAt x.1) x.1 (f x), ?_⟩
  change (coefficientPrelocal IB Z).sheafify.pred
    (fun x : U => Z.coordChange i (Z.indexAt x.1) x.1 (f x))
  apply TopCat.PrelocalPredicate.sheafifyOf
  intro j
  have hChange : ContMDiffOn IB 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
      (fun x : U => Z.coordChange i j x.1)
      {x : U | x.1 ∈ Z.baseSet j} :=
    (Z.contMDiffOn_coordChange IB i j).comp
      contMDiff_subtype_val.contMDiffOn
      (fun x hx => ⟨hU x.2, hx⟩)
  apply (hChange.clm_apply f.contMDiff.contMDiffOn).congr
  intro x hx
  exact Z.coordChange_comp i (Z.indexAt x.1) j x.1
    ⟨⟨hU x.2, Z.mem_baseSet_at x.1⟩, hx⟩ (f x)

/-- A local frame identifies the actual section module with its scalar
ring. This is linear over holomorphic functions, not merely over ℂ. -/
def coordinateLinearEquiv (i : ι) (U : Opens B)
    (hU : (U : Set B) ⊆ Z.baseSet i) :
    sectionSubmodule IB Z U ≃ₗ[Functions IB U] Functions IB U where
  toFun s := ⟨coefficient Z i s.1, coefficient_holomorphic_of_le IB Z i U hU s⟩
  invFun := sectionOfFunction IB Z i U hU
  left_inv s := by
    apply Subtype.ext
    funext x
    change Z.coordChange i (Z.indexAt x.1) x.1
      (Z.coordChange (Z.indexAt x.1) i x.1 (s.1 x)) = s.1 x
    rw [Z.coordChange_comp (Z.indexAt x.1) i (Z.indexAt x.1) x.1
      ⟨⟨Z.mem_baseSet_at x.1, hU x.2⟩, Z.mem_baseSet_at x.1⟩]
    exact Z.coordChange_self _ _ (Z.mem_baseSet_at x.1) _
  right_inv f := by
    apply Subtype.ext
    funext x
    change Z.coordChange (Z.indexAt x.1) i x.1
      (Z.coordChange i (Z.indexAt x.1) x.1 (f x)) = f x
    rw [Z.coordChange_comp i (Z.indexAt x.1) i x.1
      ⟨⟨hU x.2, Z.mem_baseSet_at x.1⟩, hU x.2⟩]
    exact Z.coordChange_self _ _ (hU x.2) _
  map_add' s t := by
    apply Subtype.ext
    funext x
    exact map_add _ _ _
  map_smul' f s := by
    apply Subtype.ext
    funext x
    exact map_smul (Z.coordChange (Z.indexAt x.1) i x.1) (f x) (s.1 x)

/-- These rank-one trivializations commute with every restriction inside
the chart, as required for local freeness of a sheaf, not just unrelated
isomorphisms of its section modules. -/
theorem coordinate_restrict (i : ι) (U V : Opens B)
    (hVU : V ≤ U) (hU : (U : Set B) ⊆ Z.baseSet i)
    (s : sectionSubmodule IB Z U) :
    coordinateLinearEquiv IB Z i V (fun _ hx => hU (hVU hx))
      ((moduleSheaf IB Z).val.map (homOfLE hVU).op s) =
      ContMDiffMap.restrictRingHom IB 𝓘(ℂ,ℂ) ℂ hVU
        (coordinateLinearEquiv IB Z i U hU s) := rfl

/-- Local scalar identifications use exactly the original line-bundle
transition function on overlaps. -/
theorem coordinate_transition (i j : ι) (U : Opens B)
    (hi : (U : Set B) ⊆ Z.baseSet i) (hj : (U : Set B) ⊆ Z.baseSet j)
    (s : sectionSubmodule IB Z U) (x : U) :
    coordinateLinearEquiv IB Z j U hj s x =
      HolomorphicLinePowers.transitionScalar Z i j x.1 *
        coordinateLinearEquiv IB Z i U hi s x := by
  change Z.coordChange (Z.indexAt x.1) j x.1 (s.1 x) = _
  rw [← Z.coordChange_comp (Z.indexAt x.1) i j x.1
    ⟨⟨Z.mem_baseSet_at x.1, hi x.2⟩, hj x.2⟩]
  exact HolomorphicLinePowers.linear_apply_one (Z.coordChange i j x.1) _

/-- The chart neighborhoods cover the base and carry an actual rank-one
free section-module identification. -/
theorem exists_local_rank_one (x : B) :
    ∃ U : Opens B, x ∈ U ∧
      Nonempty (sectionSubmodule IB Z U ≃ₗ[Functions IB U] Functions IB U) := by
  let i := Z.indexAt x
  let U : Opens B := ⟨Z.baseSet i, Z.isOpen_baseSet i⟩
  exact ⟨U, Z.mem_baseSet_at x, ⟨coordinateLinearEquiv IB Z i U (fun _ h => h)⟩⟩

end
end QuaternionicSymmetry.HolomorphicLineModuleLocalFree

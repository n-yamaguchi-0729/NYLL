/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-!
# Actual cover domination from the original function-field embedding

An embedding of the function field of a connected finite étale cover into
an extension of the base function field gives an actual morphism from the
normalization in that extension to the original covering scheme. Both the
generic embedding and the map to the base are retained. This is the
geometric step that turns Hilbert class-field containment into domination
of the original native cover.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y]
  {L : Type u} [Field L] [Algebra X.functionField L]

/-- The original generic source specified by the function-field embedding. -/
def finiteEtaleFieldEmbeddingSource :
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (_ : Y.left.functionField →ₐ[X.functionField] L),
    Spec (.of L) ⟶ Y.left := by
  intro integralY algebraXY i
  exact Spec.map (CommRingCat.ofHom i.toRingHom) ≫
    Y.left.fromSpecStalk (genericPoint Y.left)

/-- The source defined by the embedding lies over the original generic
extension morphism of the base. -/
@[reassoc]
theorem finiteEtaleFieldEmbeddingSource_comp :
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (i : Y.left.functionField →ₐ[X.functionField] L),
    finiteEtaleFieldEmbeddingSource Y i ≫ Y.hom = X.genericExtensionMorphism L := by
  intro integralY algebraXY i
  let π : Y.left ⟶ X := Y.hom
  have hdense : DenseRange π := finiteEtale_hom_denseRange_of_isConnected Y
  have hsquare := Spec_functionFieldMap_fromSpecStalk π hdense
  rw [finiteEtaleFieldEmbeddingSource, Category.assoc,
    ← hsquare,
    ← Category.assoc, ← Spec.map_comp]
  have hmap : CommRingCat.ofHom
      (π.functionFieldMap hdense) ≫
        CommRingCat.ofHom i.toRingHom =
      CommRingCat.ofHom (algebraMap X.functionField L) := by
    apply CommRingCat.hom_ext
    ext a
    exact i.commutes a
  rw [hmap]
  rfl

/-- Actual domination of the given finite étale cover by the normalization
in a field containing its original embedded function field. -/
def normalizationToFiniteEtaleOfFieldEmbedding :
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (_ : Y.left.functionField →ₐ[X.functionField] L),
    (X.genericExtensionMorphism L).normalization ⟶ Y.left := by
  intro integralY algebraXY i
  have hEtale : IsFiniteEtale Y.hom := Y.prop
  exact (X.genericExtensionMorphism L).normalizationDesc
    (finiteEtaleFieldEmbeddingSource Y i) Y.hom
    (finiteEtaleFieldEmbeddingSource_comp Y i).symm

/-- The domination morphism is over the original base scheme. -/
@[reassoc]
theorem normalizationToFiniteEtaleOfFieldEmbedding_comp :
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (i : Y.left.functionField →ₐ[X.functionField] L),
    normalizationToFiniteEtaleOfFieldEmbedding Y i ≫ Y.hom =
      (X.genericExtensionMorphism L).fromNormalization := by
  intro integralY algebraXY i
  have hEtale : IsFiniteEtale Y.hom := Y.prop
  exact (X.genericExtensionMorphism L).normalizationDesc_comp
    (finiteEtaleFieldEmbeddingSource Y i) Y.hom
    (finiteEtaleFieldEmbeddingSource_comp Y i).symm

/-- Its generic restriction is the specified field embedding, not a new
embedding chosen after normalization. -/
@[reassoc]
theorem toNormalization_normalizationToFiniteEtaleOfFieldEmbedding :
    let _ : IsIntegral Y.left := coverIntegral Y
    let _ : Algebra X.functionField Y.left.functionField := coverFieldAlgebra Y
    ∀ (i : Y.left.functionField →ₐ[X.functionField] L),
    (X.genericExtensionMorphism L).toNormalization ≫
        normalizationToFiniteEtaleOfFieldEmbedding Y i =
      finiteEtaleFieldEmbeddingSource Y i := by
  intro integralY algebraXY i
  have hEtale : IsFiniteEtale Y.hom := Y.prop
  exact (X.genericExtensionMorphism L).toNormalization_normalizationDesc
    (finiteEtaleFieldEmbeddingSource Y i) Y.hom
    (finiteEtaleFieldEmbeddingSource_comp Y i).symm

end EtaleFundamentalGroups

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A map from a nonempty cover to a connected cover is surjective on the
original geometric fibers. The proof uses transitivity of the actual
fundamental-group action, so it does not change the chosen base point. -/
theorem fiber_map_surjective_of_connected_target
    {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X)
    {V Y : FiniteEtale X} [Nonempty V.left] [IsConnected Y]
    (f : V ⟶ Y) : Function.Surjective ((fiber ξ).map f) := by
  let F := fiber ξ
  obtain ⟨v⟩ := (not_initial_iff_fiber_nonempty F V).mp
    (notInitial_of_nonempty_left V)
  intro y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F) (F.map f v) y
  exact ⟨g • v, (mulAction_naturality F g f v).symm.trans hg⟩

/-- A nontrivial native action on a connected cover is detected on every
nonempty cover which dominates it. -/
theorem exists_moved_fiberPoint_of_hom_to_connected
    {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (g : π₁ᵉᵗ(ξ))
    {V Y : FiniteEtale X} [Nonempty V.left] [IsConnected Y]
    (f : V ⟶ Y) (y : (fiber ξ).obj Y) (hy : g • y ≠ y) :
    ∃ v : (fiber ξ).obj V, g • v ≠ v := by
  obtain ⟨v, hv⟩ := fiber_map_surjective_of_connected_target ξ f y
  refine ⟨v, ?_⟩
  intro hfix
  apply hy
  rw [← hv]
  exact (mulAction_naturality (fiber ξ) g f v).trans
    (congrArg ((fiber ξ).map f) hfix)

end AlgebraicGeometry.FiniteEtale

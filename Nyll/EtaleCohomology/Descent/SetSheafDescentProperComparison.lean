/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentRepresentedMatchingRestriction
public import Nyll.EtaleCohomology.Descent.SetSheafDescentComparisonStalk
public import Nyll.EtaleCohomology.Descent.SetSheafDescentRepresenter
public import Nyll.EtaleCohomology.Descent.SetSheafSplitDescent

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSections
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberComponent
public import Nyll.EtaleCohomology.Descent.RepresentedFiberStalkComponent
public import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The actual proper descent comparison is an isomorphism

The original matching-stalk inclusion restricts bijectively to every
geometric lift. The existing unit-component isomorphism identifies this
map with the original descent counit. Conservativity of geometric points
and the existing equivalence counit then recover the original coefficient
sheaf with its specified overlap, over an arbitrary scheme base.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology.SetSheafDescent

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [IsProper q]
  (V : FiniteEtale Y)
  (η : (etaleBaseChange (pullback.fst q q)).obj ((finiteEtaleToEtale Y).obj V) ≅
    (etaleBaseChange (pullback.snd q q)).obj ((finiteEtaleToEtale Y).obj V))
  (hunit : FiniteEtale.pairHom q ((FiniteEtale.forget Y).obj V)
      ((Scheme.Etale.forget (pullback q q)).map η.hom) (𝟙 Y) (𝟙 Y) rfl = 𝟙 _)
  (htriple :
    FiniteEtale.pairHom q ((FiniteEtale.forget Y).obj V)
        ((Scheme.Etale.forget (pullback q q)).map η.hom)
        (FiniteEtale.radicialTripleFirst q) (FiniteEtale.radicialTripleSecond q)
        (FiniteEtale.radicialTriple_first_second q) ≫
      FiniteEtale.pairHom q ((FiniteEtale.forget Y).obj V)
        ((Scheme.Etale.forget (pullback q q)).map η.hom)
        (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTripleThird q)
        (FiniteEtale.radicialTriple_second_third q) =
      FiniteEtale.pairHom q ((FiniteEtale.forget Y).obj V)
        ((Scheme.Etale.forget (pullback q q)).map η.hom)
        (FiniteEtale.radicialTripleFirst q) (FiniteEtale.radicialTripleThird q)
        (FiniteEtale.radicialTriple_first_third q))

include hunit htriple in
/-- The actual counit comparison for a represented finite étale
coefficient is an isomorphism at every geometric point of the source. -/
theorem represented_comparison_stalk_isIso
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (CommRingCat.of Ω) ⟶ Y) :
    IsIso ((Scheme.pointSmallEtale y).sheafFiber.map
      (comparison q ((finiteEtaleSheaf Y).obj V)
        (representedOverlapIso q ((finiteEtaleToEtale Y).obj V) η))) := by
  let W := (finiteEtaleToEtale Y).obj V
  let F := (finiteEtaleSheaf Y).obj V
  let θ := representedOverlapIso q W η
  let Φ := Scheme.pointSmallEtale (y ≫ q)
  let Ψ := Scheme.pointSmallEtale y
  let i := Φ.sheafFiber.map (inclusion q F θ)
  let k := etalePushforwardStalkComponent q (y ≫ q) ⟨y, rfl⟩ F
  let E : Ψ.sheafFiber.obj F ≅ Ψ.fiber.obj W :=
    (representableSheafFiberIso Ψ).app W
  let C := etaleSetPushforwardRepresentableFiberSections q (y ≫ q) W
  let r := representedGeometricFiberRestriction q (y ≫ q) y rfl W
  have hbij : Function.Bijective (i ≫ C ≫ r) :=
    represented_matchingStalk_restriction_bijective q (y ≫ q) V η hunit htriple y rfl
  have hC : k ≫ E.hom = C ≫ r :=
    etaleSetPushforwardRepresentableFiberSections_component q (y ≫ q) y rfl W
  have heq : (i ≫ k) ≫ E.hom = i ≫ C ≫ r :=
    (Category.assoc i k E.hom).trans (congrArg (fun a => i ≫ a) hC)
  have hcomp : IsIso ((i ≫ k) ≫ E.hom) :=
    heq.symm ▸ (CategoryTheory.isIso_iff_bijective (i ≫ C ≫ r)).mpr hbij
  have hE : IsIso E.hom := E.isIso_hom
  have hi : IsIso (i ≫ k) :=
    (@isIso_comp_right_iff (Type u) _ _ _ _ (i ≫ k) E.hom hE).mp hcomp
  exact (comparison_stalk_isIso_iff q F θ y).mpr hi

include hunit htriple in
/-- The actual proper descent comparison recovers every represented
finite étale coefficient with its original overlap action. -/
theorem represented_comparison_isIso :
    IsIso (comparison q ((finiteEtaleSheaf Y).obj V)
      (representedOverlapIso q ((finiteEtaleToEtale Y).obj V) η)) := by
  let Ω : Y → Type u := fun y => AlgebraicClosure (Y.residueField y)
  let s : ∀ y : Y, Spec (CommRingCat.of (Ω y)) ⟶ Y := fun y =>
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (Ω y))) ≫
      Y.fromSpecResidueField y
  have hs (y : Y) : s y default = y := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply y _
  have hcover : ⋃ y : Y, Set.range (s y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact Set.mem_iUnion.mpr ⟨y, default, hs y⟩
  have hpoints := Scheme.isConservative_pointSmallEtale s hcover
  apply (hpoints.jointlyReflectIsomorphisms_type.isIso_iff
    (comparison q ((finiteEtaleSheaf Y).obj V)
      (representedOverlapIso q ((finiteEtaleToEtale Y).obj V) η))).mpr
  rintro ⟨_, ⟨y⟩⟩
  exact represented_comparison_stalk_isIso q V η hunit htriple (s y)

variable (G : EtaleFiniteLocallyConstantSetSheaf Y)
  (θ : (etaleSetPullback (pullback.fst q q)).obj G.obj ≅
    (etaleSetPullback (pullback.snd q q)).obj G.obj)

/-- The original matching-sheaf counit recovers the original finite
locally constant coefficient under a proper cover. Its only descent
condition is the original triple cocycle. -/
theorem comparison_isIso_of_proper_surjective
    (htriple :
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
          (FiniteEtale.radicialTripleSecond q) (FiniteEtale.radicialTriple_first_second q) ≪≫
        sheafPairIso q G.obj θ (FiniteEtale.radicialTripleSecond q)
          (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_second_third q) =
      sheafPairIso q G.obj θ (FiniteEtale.radicialTripleFirst q)
        (FiniteEtale.radicialTripleThird q) (FiniteEtale.radicialTriple_first_third q)) :
    IsIso (comparison q G.obj θ) := by
  let V := (finiteEtaleEquivFiniteLocallyConstantSetSheaf Y).inverse.obj G
  let η := (finiteEtaleToEtale (pullback q q)).mapIso
    (overlapRepresenterIso G (pullback.fst q q) (pullback.snd q q) θ)
  have hunit := overlapRepresenter_pairHom_diagonal_of_triple q G θ htriple
  have htr := overlapRepresenter_pairHom_triple q G θ htriple
  have hrep : IsIso (comparison q ((finiteEtaleSheaf Y).obj V)
      (representedOriginalOverlap q G θ)) :=
    represented_comparison_isIso q V η hunit htr
  have hmap : IsIso
      ((etaleSetPullback q).map (matchingSheafRepresenterIso q G θ).hom ≫
        comparison q ((finiteEtaleSheaf Y).obj V) (representedOriginalOverlap q G θ)) :=
    inferInstance
  have hcomp : IsIso (comparison q G.obj θ ≫ (representerSheafIso G).hom) :=
    (matchingSheafRepresenterIso_comparison q G θ) ▸ hmap
  exact (isIso_comp_right_iff (comparison q G.obj θ) (representerSheafIso G).hom).mp hcomp

end EtaleCohomology.SetSheafDescent

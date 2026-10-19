/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Torus
import Nyll.SchemeTheory.Morphisms.OverPullbackDescent
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Actual semiabelian extensions

An extension consists of actual group-scheme homomorphisms, a torus identified by
the universal property of the identity kernel, and a smooth surjective projection
to an abelian variety. The resulting exactness holds on every parameter scheme.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- An actual extension of an abelian variety by a torus, with its kernel universal property. -/
structure SemiabelianExtension (G : CommGrp (Over (Spec (CommRingCat.of K)))) where
  /-- The torus kernel. -/
  torus : CommGrp (Over (Spec (CommRingCat.of K)))
  /-- The kernel has a geometric splitting as an actual torus. -/
  [torus_isTorus : IsTorus torus]
  /-- The abelian quotient. -/
  quotient : CommGrp (Over (Spec (CommRingCat.of K)))
  /-- The quotient is smooth, proper and geometrically connected. -/
  [quotient_isAbelian : IsAbelianScheme quotient]
  /-- The actual inclusion of the kernel. -/
  inclusion : torus ⟶ G
  /-- The actual quotient homomorphism. -/
  projection : G ⟶ quotient
  /-- The kernel maps to the identity of the quotient. -/
  condition : inclusion.hom.hom.hom ≫ projection.hom.hom.hom = 1
  /-- Every point mapping to the identity factors uniquely through the given torus. -/
  isKernel : IsLimit (Fork.ofι inclusion.hom.hom.hom
    (condition.trans (MonObj.comp_one inclusion.hom.hom.hom).symm))
  /-- The actual quotient morphism is smooth. -/
  projection_smooth : Smooth projection.hom.hom.hom.left
  /-- The actual quotient morphism is surjective. -/
  projection_surjective : Surjective projection.hom.hom.hom.left

attribute [instance] SemiabelianExtension.torus_isTorus
  SemiabelianExtension.quotient_isAbelian

/-- A semiabelian variety admits an actual torus-by-abelian extension. -/
class IsSemiabelian (G : CommGrp (Over (Spec (CommRingCat.of K)))) : Prop where
  /-- An actual torus-by-abelian extension of this group scheme. -/
  exists_extension : Nonempty (SemiabelianExtension G)

namespace SemiabelianExtension

variable {G : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- An actual extension supplies semiabelianity of its middle group. -/
theorem isSemiabelian (E : SemiabelianExtension G) : IsSemiabelian G := ⟨⟨E⟩⟩

/-- The kernel inclusion is a monomorphism of actual schemes over the base. -/
theorem inclusion_mono (E : SemiabelianExtension G) : Mono E.inclusion.hom.hom.hom :=
  Fork.IsLimit.mono E.isKernel

/-- Exactness holds on every parameter scheme, with no lifting assumption on that scheme. -/
theorem point_exact (E : SemiabelianExtension G) (T : Over (Spec (CommRingCat.of K))) :
    Set.range (fun f : T ⟶ E.torus.X => f ≫ E.inclusion.hom.hom.hom) =
      {g : T ⟶ G.X | g ≫ E.projection.hom.hom.hom = 1} := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    change (f ≫ E.inclusion.hom.hom.hom) ≫ E.projection.hom.hom.hom = 1
    rw [Category.assoc, E.condition, MonObj.comp_one]
  · intro hg
    let h : g ≫ E.projection.hom.hom.hom = g ≫ (1 : G.X ⟶ E.quotient.X) :=
      hg.trans (MonObj.comp_one g).symm
    exact ⟨Fork.IsLimit.lift E.isKernel g h, Fork.IsLimit.lift_ι' E.isKernel g h⟩

/-- Smoothness of the middle group follows from its actual quotient projection. -/
theorem smooth (E : SemiabelianExtension G) : Smooth G.X.hom := by
  have : Smooth E.projection.hom.hom.hom.left := E.projection_smooth
  have h : Smooth (E.projection.hom.hom.hom.left ≫ E.quotient.X.hom) := inferInstance
  rw [Over.w E.projection.hom.hom.hom] at h
  exact h

/-- Field extension transports the actual extension and its kernel universal property. -/
def baseChange (E : SemiabelianExtension G) {L : Type u} [Field L]
    (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) :
    SemiabelianExtension ((GroupSchemes.baseChange f).obj G) where
  torus := (GroupSchemes.baseChange f).obj E.torus
  quotient := (GroupSchemes.baseChange f).obj E.quotient
  inclusion := (GroupSchemes.baseChange f).map E.inclusion
  projection := (GroupSchemes.baseChange f).map E.projection
  condition := by
    exact ((Over.pullback f).map_comp E.inclusion.hom.hom.hom
      E.projection.hom.hom.hom).symm.trans
        ((congrArg (Over.pullback f).map E.condition).trans ((Over.pullback f).map_one))
  isKernel := by
    have h := isLimitForkMapOfIsLimit (Over.pullback f)
      (E.condition.trans (MonObj.comp_one E.inclusion.hom.hom.hom).symm) E.isKernel
    refine Fork.isLimitOfIsos _ h _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact (Category.id_comp _).trans
        ((Over.pullback f).map_one.symm.trans (Category.comp_id _).symm)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  projection_smooth := MorphismProperty.of_isPullback
    (overPullback_map_isPullback f E.projection.hom.hom.hom).flip E.projection_smooth
  projection_surjective := MorphismProperty.of_isPullback
    (overPullback_map_isPullback f E.projection.hom.hom.hom).flip E.projection_surjective

end SemiabelianExtension

namespace IsSemiabelian

variable {G : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- Every semiabelian variety is smooth over its ground field. -/
instance smooth [IsSemiabelian G] : Smooth G.X.hom := by
  obtain ⟨E⟩ := exists_extension (G := G)
  exact E.smooth

/-- Every field extension preserves semiabelianity on the actual group pullback. -/
instance baseChange {L : Type u} [Field L]
    (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) [IsSemiabelian G] :
    IsSemiabelian ((GroupSchemes.baseChange f).obj G) := by
  obtain ⟨E⟩ := exists_extension (G := G)
  exact (E.baseChange f).isSemiabelian

end IsSemiabelian

end AlgebraicGeometry

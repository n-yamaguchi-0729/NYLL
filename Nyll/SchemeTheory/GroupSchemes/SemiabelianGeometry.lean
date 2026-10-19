/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Semiabelian
import Nyll.SchemeTheory.GroupSchemes.KernelTranslation
import Nyll.SchemeTheory.GroupSchemes.TorusGeometry
import Nyll.SchemeTheory.GroupSchemes.TorusSeparatedQuasiCompact
import Nyll.SchemeTheory.Morphisms.GeometricallyConnectedDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Geometry of actual semiabelian extensions

Translation identifies the pullback of the quotient map along itself with the
projection from the product with its torus kernel. Descent therefore supplies
geometric connectedness, separatedness and quasi-compactness of the quotient map
and of the actual middle group.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {G : CommGrp (Over (Spec (CommRingCat.of K)))}

namespace SemiabelianExtension

private theorem projection_property (E : SemiabelianExtension G)
    (P Q : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.DescendsAlong Q]
    (ht : P E.torus.X.hom) (hq : Q E.projection.hom.hom.hom.left) :
    P E.projection.hom.hom.hom.left := by
  let a := GroupSchemes.kernelTranslation (𝟙 G) E.inclusion
  let p := E.projection.hom.hom.hom
  have h : IsPullback a (Limits.prod.fst (X := G.X) (Y := E.torus.X)) p p := by
    have h := GroupSchemes.kernelTranslation_isPullback
      (𝟙 G) E.inclusion E.projection E.condition E.isKernel
    change IsPullback a (Limits.prod.fst (X := G.X) (Y := E.torus.X)) p
      ((𝟙 G.X) ≫ p) at h
    rw [Category.id_comp] at h
    exact h
  have hs := h.map (Over.forget (Spec (CommRingCat.of K)))
  have hprod := Over.isPullback_of_binaryFan_isLimit _ (Limits.prodIsProd G.X E.torus.X)
  have hp : P (Limits.prod.fst (X := G.X) (Y := E.torus.X)).left :=
    MorphismProperty.of_isPullback hprod.flip ht
  exact MorphismProperty.of_isPullback_of_descendsAlong hs.flip hq hp

private theorem projection_fppf_property (E : SemiabelianExtension G)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [IsZariskiLocalAtTarget P]
    (hd : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact))
    (ht : P E.torus.X.hom) : P E.projection.hom.hom.hom.left := by
  have : Smooth E.projection.hom.hom.hom.left := E.projection_smooth
  have : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := hd
  have : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := inferInstance
  exact E.projection_property P (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ht ⟨⟨E.projection_surjective, inferInstance⟩, inferInstance⟩

/-- The actual quotient has geometrically connected fibres, detected by translation. -/
theorem projection_geometricallyConnected (E : SemiabelianExtension G) :
    GeometricallyConnected E.projection.hom.hom.hom.left :=
  E.projection_property (@GeometricallyConnected) (@Surjective)
    (inferInstanceAs (GeometricallyConnected E.torus.X.hom)) E.projection_surjective

/-- The actual quotient is separated, by descent from its torus translation model. -/
theorem projection_isSeparated (E : SemiabelianExtension G) :
    IsSeparated E.projection.hom.hom.hom.left :=
  E.projection_fppf_property (@IsSeparated) IsSeparated.descendsAlong_fpqc
    (inferInstanceAs (IsSeparated E.torus.X.hom))

/-- The actual quotient is quasi-compact; quasi-compactness of its cover is not an assumption. -/
theorem projection_quasiCompact (E : SemiabelianExtension G) :
    QuasiCompact E.projection.hom.hom.hom.left := by
  have hAff : HasAffineProperty (@QuasiCompact : MorphismProperty Scheme.{u})
      (fun X _ _ _ => CompactSpace X) :=
    AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget
      (@QuasiCompact : MorphismProperty Scheme.{u}) (fun X _ _ _ => CompactSpace X) hAff
  exact E.projection_fppf_property (@QuasiCompact) QuasiCompact.descendsAlong_fpqc
    (inferInstanceAs (QuasiCompact E.torus.X.hom))

/-- The middle group of an actual semiabelian extension is geometrically connected. -/
theorem geometricallyConnected (E : SemiabelianExtension G) :
    GeometricallyConnected G.X.hom := by
  have : GeometricallyConnected E.projection.hom.hom.hom.left :=
    E.projection_geometricallyConnected
  have : Smooth E.projection.hom.hom.hom.left := E.projection_smooth
  have h := GeometricallyConnected.comp E.projection.hom.hom.hom.left E.quotient.X.hom
  rw [Over.w E.projection.hom.hom.hom] at h
  exact h

/-- The middle group of an actual semiabelian extension is separated. -/
theorem isSeparated (E : SemiabelianExtension G) : IsSeparated G.X.hom := by
  have : IsSeparated E.projection.hom.hom.hom.left := E.projection_isSeparated
  have h : IsSeparated (E.projection.hom.hom.hom.left ≫ E.quotient.X.hom) := inferInstance
  rw [Over.w E.projection.hom.hom.hom] at h
  exact h

/-- The middle group of an actual semiabelian extension is quasi-compact. -/
theorem quasiCompact (E : SemiabelianExtension G) : QuasiCompact G.X.hom := by
  have : QuasiCompact E.projection.hom.hom.hom.left := E.projection_quasiCompact
  have h : QuasiCompact (E.projection.hom.hom.hom.left ≫ E.quotient.X.hom) := inferInstance
  rw [Over.w E.projection.hom.hom.hom] at h
  exact h

end SemiabelianExtension

namespace IsSemiabelian

/-- Every semiabelian variety is geometrically connected. -/
instance geometricallyConnected [IsSemiabelian G] : GeometricallyConnected G.X.hom := by
  obtain ⟨E⟩ := exists_extension (G := G)
  exact E.geometricallyConnected

/-- Every semiabelian variety is separated over its ground field. -/
instance isSeparated [IsSemiabelian G] : IsSeparated G.X.hom := by
  obtain ⟨E⟩ := exists_extension (G := G)
  exact E.isSeparated

/-- Every semiabelian variety is quasi-compact over its ground field. -/
instance quasiCompact [IsSemiabelian G] : QuasiCompact G.X.hom := by
  obtain ⟨E⟩ := exists_extension (G := G)
  exact E.quasiCompact

/-- A semiabelian variety has a connected actual underlying topological space. -/
instance connectedSpace [IsSemiabelian G] : ConnectedSpace G.X.left :=
  GeometricallyConnected.connectedSpace_of_subsingleton G.X.hom

/-- A semiabelian variety has a quasi-compact actual underlying topological space. -/
instance compactSpace [IsSemiabelian G] : CompactSpace G.X.left :=
  QuasiCompact.compactSpace_of_compactSpace G.X.hom

end IsSemiabelian

end AlgebraicGeometry

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Torus
import Nyll.SchemeTheory.GroupSchemes.SplitTorusSmooth
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometry of actual tori over fields

Smoothness descends from the split torus over an algebraic closure. Connectedness
descends along the surjective field extension, and the same proof on every base
change proves geometric connectedness.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace GroupSchemes

/-- The actual split torus over a field is connected because its character algebra is a domain. -/
instance splitTorus_connectedSpace (K : Type u) [Field K] (r : ℕ) :
    ConnectedSpace (splitTorus K r).X.left := by
  change ConnectedSpace (Spec (CommRingCat.of (splitTorusAlgebra K r)))
  infer_instance

end GroupSchemes

variable {K : Type u} [Field K] {G : CommGrp (Over (Spec (CommRingCat.of K)))}

namespace IsSplitTorus

/-- Every actual split torus is smooth over its ground field. -/
instance smooth [IsSplitTorus G] : Smooth G.X.hom := by
  obtain ⟨r, ⟨e⟩⟩ := exists_split (G := G)
  exact GroupSchemes.property_of_overIso (@Smooth)
    ((CommGrp.forget _).mapIso e.symm)
    (inferInstanceAs (Smooth (GroupSchemes.splitTorus K r).X.hom))

end IsSplitTorus

namespace IsTorus

/-- Smoothness of the actual torus descends from its geometric split model. -/
instance smooth [IsTorus G] : Smooth G.X.hom := by
  let Ω := AlgebraicClosure K
  let f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Surjective f := ⟨fun y => ⟨default, Subsingleton.elim _ y⟩⟩
  have : IsSplitTorus ((GroupSchemes.baseChange f).obj G) := geometric_split Ω f
  have h : Smooth (pullback.snd G.X.hom f) :=
    inferInstanceAs (Smooth ((GroupSchemes.baseChange f).obj G).X.hom)
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback G.X.hom f).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

/-- Every torus has a connected actual underlying scheme. -/
instance connectedSpace [IsTorus G] : ConnectedSpace G.X.left := by
  let Ω := AlgebraicClosure K
  let f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Surjective f := ⟨fun y => ⟨default, Subsingleton.elim _ y⟩⟩
  obtain ⟨r, hr⟩ := exists_geometric_split (G := G)
  obtain ⟨e⟩ := hr Ω f
  let a := (CommGrp.forget _ ⋙ Over.forget _).mapIso e
  have : ConnectedSpace ↥(pullback G.X.hom f : Scheme.{u}) :=
    a.hom.homeomorph.connectedSpace_iff.mpr
      (inferInstanceAs (ConnectedSpace (GroupSchemes.splitTorus Ω r).X.left))
  let q : (pullback G.X.hom f : Scheme.{u}) ⟶ G.X.left := pullback.fst G.X.hom f
  exact q.surjective.connectedSpace q.continuous

/-- Every torus is geometrically connected over its ground field. -/
instance geometricallyConnected [IsTorus G] : GeometricallyConnected G.X.hom := by
  constructor
  apply (geometrically_iff_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X) (f := G.X.hom)).mpr
  intro L _ f
  exact inferInstanceAs (ConnectedSpace ((GroupSchemes.baseChange f).obj G).X.left)

end IsTorus

end AlgebraicGeometry

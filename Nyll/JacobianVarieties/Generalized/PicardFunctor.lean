/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# The naive Picard presheaf with chosen modulus trivializations

For every test scheme over the affine base, objects carry an actual trivialization along the
base change of the whole modulus scheme. The transition functions preserve that data.
This is the presheaf of compatible-isomorphism classes, before fppf sheafification; it is not
asserted to be a representing scheme or the relative Picard sheaf when the modulus is empty.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem classesPullback_congr {X X' D D' : Scheme.{u}}
    {i : D ⟶ X} {i' : D' ⟶ X'}
    {f f' : X' ⟶ X} {g g' : D' ⟶ D} (hf : f = f') (hg : g = g')
    (w : i' ≫ f = g ≫ i) (w' : i' ≫ f' = g' ≫ i)
    (x : RigidifiedLineBundle.Classes i) :
    RigidifiedLineBundle.classesPullback f g w x =
      RigidifiedLineBundle.classesPullback f' g' w' x := by
  cases hf
  cases hg
  rfl

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X)

/-- The full scheme-theoretic modulus after base change. -/
def modulusBaseChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (i ≫ c) t ⟶ pullback c t :=
  pullback.map (i ≫ c) t c t i (𝟙 T) (𝟙 _)
    (Category.comp_id (i ≫ c))
    ((Category.comp_id t).trans (Category.id_comp t).symm)

/-- Modulus inclusions commute with change of the test scheme. -/
theorem modulusBaseChange_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (s : SchemeHomOver t' t) :
    modulusBaseChange c i t' ≫ RelPicard.baseChangeSnd c s =
      RelPicard.baseChangeSnd (i ≫ c) s ≫ modulusBaseChange c i t := by
  apply pullback.hom_ext
  · simp only [modulusBaseChange, RelPicard.baseChangeSnd, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [modulusBaseChange, RelPicard.baseChangeSnd, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

/-- Naive compatible-isomorphism classes of line bundles with a chosen modulus trivialization. -/
def modulusPicardPresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) where
  obj T := RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom)
  map {T T'} s := TypeCat.ofHom
    (RigidifiedLineBundle.classesPullback
      (RelPicard.baseChangeSnd c
        (⟨s.unop.left, Over.w s.unop⟩ : SchemeHomOver T'.unop.hom T.unop.hom))
      (RelPicard.baseChangeSnd (i ≫ c)
        (⟨s.unop.left, Over.w s.unop⟩ : SchemeHomOver T'.unop.hom T.unop.hom))
      (modulusBaseChange_naturality c i
        (⟨s.unop.left, Over.w s.unop⟩ : SchemeHomOver T'.unop.hom T.unop.hom)))
  map_id T := TypeCat.homEquiv.injective (funext fun x => by
    change RigidifiedLineBundle.classesPullback
      (RelPicard.baseChangeSnd c
        (⟨𝟙 T.unop.left, Category.id_comp T.unop.hom⟩ : SchemeHomOver _ _))
      (RelPicard.baseChangeSnd (i ≫ c)
        (⟨𝟙 T.unop.left, Category.id_comp T.unop.hom⟩ : SchemeHomOver _ _)) _ x = x
    simp only [RelPicard.baseChangeSnd_id]
    exact RigidifiedLineBundle.classesPullback_id x)
  map_comp {T T' T''} s r := TypeCat.homEquiv.injective (funext fun x => by
    let s' : SchemeHomOver T'.unop.hom T.unop.hom := ⟨s.unop.left, Over.w s.unop⟩
    let r' : SchemeHomOver T''.unop.hom T'.unop.hom := ⟨r.unop.left, Over.w r.unop⟩
    change RigidifiedLineBundle.classesPullback
      (RelPicard.baseChangeSnd c (RelPicard.postComp s' r'))
      (RelPicard.baseChangeSnd (i ≫ c) (RelPicard.postComp s' r')) _ x =
      RigidifiedLineBundle.classesPullback
        (RelPicard.baseChangeSnd c r') (RelPicard.baseChangeSnd (i ≫ c) r') _
        (RigidifiedLineBundle.classesPullback
          (RelPicard.baseChangeSnd c s') (RelPicard.baseChangeSnd (i ≫ c) s') _ x)
    exact (classesPullback_congr
      (RelPicard.baseChangeSnd_comp c s' r').symm
      (RelPicard.baseChangeSnd_comp (i ≫ c) s' r').symm _ _ x).trans
      (RigidifiedLineBundle.classesPullback_comp
      (RelPicard.baseChangeSnd c s') (RelPicard.baseChangeSnd (i ≫ c) s')
      (modulusBaseChange_naturality c i s')
      (RelPicard.baseChangeSnd c r') (RelPicard.baseChangeSnd (i ≫ c) r')
      (modulusBaseChange_naturality c i r') x).symm)

end AlgebraicGeometry.GeneralizedJacobian

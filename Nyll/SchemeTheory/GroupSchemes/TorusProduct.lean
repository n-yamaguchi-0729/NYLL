/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Torus
import Nyll.SchemeTheory.GroupSchemes.SplitTorusSchemePoints
import Nyll.SchemeTheory.CategoryTheory.CommGroupPoints
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Products of actual torus group schemes -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GroupSchemes

variable {S S' : Scheme.{u}}

/-- Isomorphisms of group schemes induce the actual componentwise product isomorphism. -/
def productIso {G G' H H' : CommGrp (Over S)} (e : G ≅ G') (d : H ≅ H') :
    product G H ≅ product G' H' := by
  let a : G.X ≅ G'.X := (CommGrp.forget (Over S)).mapIso e
  let b : H.X ≅ H'.X := (CommGrp.forget (Over S)).mapIso d
  have : IsMonHom a.hom := e.hom.hom.hom.isMonHom_hom
  have : IsMonHom b.hom := d.hom.hom.hom.isMonHom_hom
  have : IsMonHom (tensorIso a b).hom := by
    change IsMonHom (a.hom ⊗ₘ b.hom)
    infer_instance
  exact CommGrp.mkIso' (tensorIso a b)

/-- Group base change preserves the actual componentwise product. -/
def baseChangeProductIso (f : S' ⟶ S) (G H : CommGrp (Over S)) :
    (baseChange f).obj (product G H) ≅ product ((baseChange f).obj G) ((baseChange f).obj H) := by
  let e := Functor.Monoidal.μIso (Over.pullback f) G.X H.X
  have : IsMonHom e.hom := by
    change IsMonHom (Functor.LaxMonoidal.μ (Over.pullback f) G.X H.X)
    infer_instance
  exact (CommGrp.mkIso' e).symm

/-- Restricting coordinates to the two blocks preserves multiplication. -/
def splitCoordinates (M : Type u) [Mul M] (r s : ℕ) :
    (Fin (r + s) → M) ≃* ((Fin r → M) × (Fin s → M)) where
  toEquiv := (Fin.appendEquiv r s).symm
  map_mul' _ _ := rfl

variable (R : Type u) [CommRing R] (r s : ℕ)

/-- Concatenating actual unit coordinates identifies points of the product split torus. -/
def splitTorusProductPointEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (product (splitTorus R r) (splitTorus R s)).X) ≃*
      (T ⟶ (splitTorus R (r + s)).X) :=
  (SchemeTheory.CommGroupPoints.productPointEquiv (splitTorus R r) (splitTorus R s) T).trans
    (((splitTorusPointEquiv R r T).prodCongr (splitTorusPointEquiv R s T)).trans
      ((splitCoordinates (((algΓ (CommRingCat.of R)).obj T).unopˣ) r s).symm.trans
        (splitTorusPointEquiv R (r + s) T).symm))

private theorem splitTorusProductPointEquiv_left (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (product (splitTorus R r) (splitTorus R s)).X) (i : Fin r) :
    splitTorusPointEquiv R (r + s) T (splitTorusProductPointEquiv R r s T x)
        (Fin.castAdd s i) =
      splitTorusPointEquiv R r T (x ≫ fst _ _) i := by
  change splitTorusPointEquiv R (r + s) T
    ((splitTorusPointEquiv R (r + s) T).symm
      (Fin.append (splitTorusPointEquiv R r T (x ≫ fst _ _))
        (splitTorusPointEquiv R s T (x ≫ snd _ _)))) (Fin.castAdd s i) = _
  rw [MulEquiv.apply_symm_apply, Fin.append_left]

private theorem splitTorusProductPointEquiv_right (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (product (splitTorus R r) (splitTorus R s)).X) (i : Fin s) :
    splitTorusPointEquiv R (r + s) T (splitTorusProductPointEquiv R r s T x)
        (Fin.natAdd r i) =
      splitTorusPointEquiv R s T (x ≫ snd _ _) i := by
  change splitTorusPointEquiv R (r + s) T
    ((splitTorusPointEquiv R (r + s) T).symm
      (Fin.append (splitTorusPointEquiv R r T (x ≫ fst _ _))
        (splitTorusPointEquiv R s T (x ≫ snd _ _)))) (Fin.natAdd r i) = _
  rw [MulEquiv.apply_symm_apply, Fin.append_right]

private theorem splitTorusProductPointEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T ⟶ T')
    (x : T' ⟶ (product (splitTorus R r) (splitTorus R s)).X) :
    splitTorusProductPointEquiv R r s T (f ≫ x) =
      f ≫ splitTorusProductPointEquiv R r s T' x := by
  apply (splitTorusPointEquiv R (r + s) T).injective
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · calc
      _ = splitTorusPointEquiv R r T ((f ≫ x) ≫ fst _ _) i :=
        splitTorusProductPointEquiv_left R r s T (f ≫ x) i
      _ = splitTorusPointEquiv R r T (f ≫ (x ≫ fst _ _)) i :=
        congrArg (fun y => splitTorusPointEquiv R r T y i) (Category.assoc _ _ _)
      _ = Units.map (((algΓ (CommRingCat.of R)).map f).unop.hom.toRingHom.toMonoidHom)
          (splitTorusPointEquiv R r T' (x ≫ fst _ _) i) :=
        splitTorusPointEquiv_naturality R r f (x ≫ fst _ _) i
      _ = Units.map (((algΓ (CommRingCat.of R)).map f).unop.hom.toRingHom.toMonoidHom)
          (splitTorusPointEquiv R (r + s) T' (splitTorusProductPointEquiv R r s T' x)
            (Fin.castAdd s i)) :=
        congrArg _ (splitTorusProductPointEquiv_left R r s T' x i).symm
      _ = _ := (splitTorusPointEquiv_naturality R (r + s) f
        (splitTorusProductPointEquiv R r s T' x) (Fin.castAdd s i)).symm
  · calc
      _ = splitTorusPointEquiv R s T ((f ≫ x) ≫ snd _ _) i :=
        splitTorusProductPointEquiv_right R r s T (f ≫ x) i
      _ = splitTorusPointEquiv R s T (f ≫ (x ≫ snd _ _)) i :=
        congrArg (fun y => splitTorusPointEquiv R s T y i) (Category.assoc _ _ _)
      _ = Units.map (((algΓ (CommRingCat.of R)).map f).unop.hom.toRingHom.toMonoidHom)
          (splitTorusPointEquiv R s T' (x ≫ snd _ _) i) :=
        splitTorusPointEquiv_naturality R s f (x ≫ snd _ _) i
      _ = Units.map (((algΓ (CommRingCat.of R)).map f).unop.hom.toRingHom.toMonoidHom)
          (splitTorusPointEquiv R (r + s) T' (splitTorusProductPointEquiv R r s T' x)
            (Fin.natAdd r i)) :=
        congrArg _ (splitTorusProductPointEquiv_right R r s T' x i).symm
      _ = _ := (splitTorusPointEquiv_naturality R (r + s) f
        (splitTorusProductPointEquiv R r s T' x) (Fin.natAdd r i)).symm

/-- The actual product of rank-r and rank-s split tori is the rank-(r+s) split torus. -/
def splitTorusProductIso : product (splitTorus R r) (splitTorus R s) ≅ splitTorus R (r + s) :=
  SchemeTheory.CommGroupPoints.isoOfPointEquiv _ _ (splitTorusProductPointEquiv R r s)
    (splitTorusProductPointEquiv_naturality R r s)

end AlgebraicGeometry.GroupSchemes

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {G H : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- Products of split tori are split, with the ranks added. -/
instance IsSplitTorus.product [IsSplitTorus G] [IsSplitTorus H] :
    IsSplitTorus (GroupSchemes.product G H) := by
  obtain ⟨r, ⟨e⟩⟩ := IsSplitTorus.exists_split (G := G)
  obtain ⟨s, ⟨d⟩⟩ := IsSplitTorus.exists_split (G := H)
  exact ⟨r + s, ⟨GroupSchemes.productIso e d ≪≫ GroupSchemes.splitTorusProductIso K r s⟩⟩

/-- Products of geometric tori retain an actual geometric splitting of fixed rank. -/
instance IsTorus.product [IsTorus G] [IsTorus H] : IsTorus (GroupSchemes.product G H) := by
  obtain ⟨r, hr⟩ := IsTorus.exists_geometric_split (G := G)
  obtain ⟨s, hs⟩ := IsTorus.exists_geometric_split (G := H)
  refine ⟨r + s, fun Ω _ _ f => ?_⟩
  obtain ⟨e⟩ := hr Ω f
  obtain ⟨d⟩ := hs Ω f
  exact ⟨GroupSchemes.baseChangeProductIso f G H ≪≫ GroupSchemes.productIso e d ≪≫
    GroupSchemes.splitTorusProductIso Ω r s⟩

end AlgebraicGeometry

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.FiniteRelativeSpec
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Morphisms between actual relative spectra

A morphism of the given sheaves of commutative rings induces the literal
`Spec` morphisms on affine sections. Their naturality gives a morphism of
the gluing diagrams and hence of the constructed colimits. When the
structure triangle commutes, this morphism is over the original base.
The construction respects identities, composition, and isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativeSpec

variable {X : Scheme.{u}} {A B C : TopCat.Sheaf CommRingCat.{u} X}

local instance diagram_isLocallyDirected (α : X.sheaf ⟶ A)
    [(underlyingModule α).IsQuasicoherent] :
    ((gluingData α).functor ⋙ Scheme.forget).IsLocallyDirected :=
  gluingData_isLocallyDirected α

/-- The sectionwise `Spec` maps form the actual morphism of gluing diagrams. -/
def diagramMap (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)
    [(underlyingModule α).IsQuasicoherent] [(underlyingModule β).IsQuasicoherent]
    (φ : A ⟶ B) : (gluingData β).functor ⟶ (gluingData α).functor :=
  Functor.whiskerRight
    (Functor.whiskerLeft (AffineZariskiSite.toOpensFunctor X).op φ.hom).rightOp Scheme.Spec

/-- The induced morphism of the constructed relative spectra. -/
def map (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)
    [(underlyingModule α).IsQuasicoherent] [(underlyingModule β).IsQuasicoherent]
    (φ : A ⟶ B) : scheme β ⟶ scheme α :=
  colimMap (diagramMap α β φ)

/-- On every affine chart the induced morphism is the spectrum of the
original algebra-section morphism. -/
@[reassoc]
theorem openCover_map (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)
    [(underlyingModule α).IsQuasicoherent] [(underlyingModule β).IsQuasicoherent]
    (φ : A ⟶ B) (U : X.AffineZariskiSite) :
    (openCover β).f U ≫ map α β φ =
      Spec.map (φ.hom.app (op U.1)) ≫ (openCover α).f U :=
  ι_colimMap (diagramMap α β φ) U

/-- The structural algebra triangle gives the original triangle over the base. -/
@[reassoc]
theorem map_toBase (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)
    [(underlyingModule α).IsQuasicoherent] [(underlyingModule β).IsQuasicoherent]
    (φ : A ⟶ B) (hφ : α ≫ φ = β) :
    map α β φ ≫ toBase α = toBase β := by
  apply colimit.hom_ext
  intro i
  let U : X.AffineZariskiSite := i
  let R : CommRingCat.{u} := X.presheaf.obj (op U.1)
  let S : CommRingCat.{u} := A.obj.obj (op U.1)
  let T : CommRingCat.{u} := B.obj.obj (op U.1)
  let a : R ⟶ S := α.hom.app (op U.1)
  let b : R ⟶ T := β.hom.app (op U.1)
  let c : S ⟶ T := φ.hom.app (op U.1)
  let jA : Spec S ⟶ scheme α := (openCover α).f U
  let jB : Spec T ⟶ scheme β := (openCover β).f U
  let k : Spec R ⟶ X := U.2.fromSpec
  let f : scheme β ⟶ scheme α := map α β φ
  let p : scheme α ⟶ X := toBase α
  let q : scheme β ⟶ X := toBase β
  have hj : jB ≫ f = Spec.map c ≫ jA := openCover_map α β φ U
  have hp : jA ≫ p = Spec.map a ≫ k := openCover_toBase α U
  have hq : jB ≫ q = Spec.map b ≫ k := openCover_toBase β U
  have hc : a ≫ c = b :=
    congrArg (fun τ : X.sheaf ⟶ B => τ.hom.app (op U.1)) hφ
  have hSpec : Spec.map c ≫ Spec.map a = Spec.map b :=
    (Spec.map_comp a c).symm.trans (congrArg (fun d : R ⟶ T => Spec.map d) hc)
  calc
    jB ≫ (f ≫ p) = (jB ≫ f) ≫ p := (Category.assoc jB f p).symm
    _ = (Spec.map c ≫ jA) ≫ p :=
      congrArg (fun d : Spec T ⟶ scheme α => d ≫ p) hj
    _ = Spec.map c ≫ (jA ≫ p) := Category.assoc (Spec.map c) jA p
    _ = Spec.map c ≫ (Spec.map a ≫ k) :=
      congrArg (fun d : Spec S ⟶ X => Spec.map c ≫ d) hp
    _ = (Spec.map c ≫ Spec.map a) ≫ k :=
      (Category.assoc (Spec.map c) (Spec.map a) k).symm
    _ = Spec.map b ≫ k := congrArg (fun d : Spec T ⟶ Spec R => d ≫ k) hSpec
    _ = jB ≫ q := hq.symm

/-- Identity morphisms of algebra sheaves induce identity scheme morphisms. -/
theorem map_id (α : X.sheaf ⟶ A) [(underlyingModule α).IsQuasicoherent] :
    map α α (𝟙 A) = 𝟙 (scheme α) := by
  apply colimit.hom_ext
  intro i
  let U : X.AffineZariskiSite := i
  let S : CommRingCat.{u} := A.obj.obj (op U.1)
  let j : Spec S ⟶ scheme α := (openCover α).f U
  have hj : j ≫ map α α (𝟙 A) = Spec.map (𝟙 S) ≫ j := openCover_map α α (𝟙 A) U
  exact hj.trans ((congrArg (fun d : Spec S ⟶ Spec S => d ≫ j) (Spec.map_id S)).trans
    ((Category.id_comp j).trans (Category.comp_id j).symm))

/-- The construction reverses composition through the original affine `Spec` maps. -/
theorem map_comp (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B) (γ : X.sheaf ⟶ C)
    [(underlyingModule α).IsQuasicoherent] [(underlyingModule β).IsQuasicoherent]
    [(underlyingModule γ).IsQuasicoherent] (φ : A ⟶ B) (ψ : B ⟶ C) :
    map α γ (φ ≫ ψ) = map β γ ψ ≫ map α β φ := by
  apply colimit.hom_ext
  intro i
  let U : X.AffineZariskiSite := i
  let R : CommRingCat.{u} := A.obj.obj (op U.1)
  let S : CommRingCat.{u} := B.obj.obj (op U.1)
  let T : CommRingCat.{u} := C.obj.obj (op U.1)
  let a : R ⟶ S := φ.hom.app (op U.1)
  let b : S ⟶ T := ψ.hom.app (op U.1)
  let jA : Spec R ⟶ scheme α := (openCover α).f U
  let jB : Spec S ⟶ scheme β := (openCover β).f U
  let jC : Spec T ⟶ scheme γ := (openCover γ).f U
  let f : scheme β ⟶ scheme α := map α β φ
  let g : scheme γ ⟶ scheme β := map β γ ψ
  let h : scheme γ ⟶ scheme α := map α γ (φ ≫ ψ)
  have hf : jB ≫ f = Spec.map a ≫ jA := openCover_map α β φ U
  have hg : jC ≫ g = Spec.map b ≫ jB := openCover_map β γ ψ U
  have hh : jC ≫ h = Spec.map (a ≫ b) ≫ jA := openCover_map α γ (φ ≫ ψ) U
  calc
    jC ≫ h = Spec.map (a ≫ b) ≫ jA := hh
    _ = (Spec.map b ≫ Spec.map a) ≫ jA :=
      congrArg (fun d : Spec T ⟶ Spec R => d ≫ jA) (Spec.map_comp a b)
    _ = Spec.map b ≫ (Spec.map a ≫ jA) := Category.assoc (Spec.map b) (Spec.map a) jA
    _ = Spec.map b ≫ (jB ≫ f) :=
      congrArg (fun d : Spec S ⟶ scheme α => Spec.map b ≫ d) hf.symm
    _ = (Spec.map b ≫ jB) ≫ f := (Category.assoc (Spec.map b) jB f).symm
    _ = (jC ≫ g) ≫ f := congrArg (fun d : Spec T ⟶ scheme β => d ≫ f) hg.symm
    _ = jC ≫ (g ≫ f) := Category.assoc jC g f

/-- An actual isomorphism of algebra sheaves gives an isomorphism of
their glued spectra, with the above original chart maps as its two morphisms. -/
def iso (α : X.sheaf ⟶ A) (β : X.sheaf ⟶ B)
    [(underlyingModule α).IsQuasicoherent] [(underlyingModule β).IsQuasicoherent]
    (e : A ≅ B) : scheme β ≅ scheme α where
  hom := map α β e.hom
  inv := map β α e.inv
  hom_inv_id :=
    (map_comp β α β e.inv e.hom).symm.trans
      ((congrArg (map β β) e.inv_hom_id).trans (map_id β))
  inv_hom_id :=
    (map_comp α β α e.hom e.inv).symm.trans
      ((congrArg (map α α) e.hom_inv_id).trans (map_id α))

end AlgebraicGeometry.Scheme.RelativeSpec

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.CategoryTheory.Yoneda

/-!
# The actual identity geometric stalk over a separably closed field

The identity geometric point is corepresented by the identity étale object.
Consequently its actual global-section germ is an isomorphism, for arbitrary
module sheaves, by the terminal-object calculation of the defining colimit.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The actual germ at the identity geometric point identifies global
sections over a separably closed field with the geometric stalk. -/
theorem etaleGlobalSectionsGerm_identity_isIso
    (k : Type u) [Field k] [IsSepClosed k]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso (etaleGlobalSectionsGerm (𝟙 (Spec (CommRingCat.of k))) Λ F) := by
  let S : Scheme.{u} := Spec (CommRingCat.of k)
  let T : S.Etale := Scheme.Etale.mk (𝟙 S)
  let Φ := Scheme.pointSmallEtale (𝟙 S)
  let ff := Functor.FullyFaithful.ofFullyFaithful (Scheme.Etale.forget S)
  let E : Φ.fiber.CorepresentableBy T :=
    { homEquiv := ff.homEquiv
      homEquiv_comp := fun g f => (Scheme.Etale.forget S).map_comp f g }
  let t₀ : Φ.fiber.obj T := E.homEquiv (𝟙 T)
  have hInitial : IsInitial (Φ.fiber.elementsMk T t₀) :=
    Functor.Elements.isInitialOfCorepresentableBy E
  have hGerm : IsIso (Φ.toPresheafFiber T t₀ F.obj) :=
    (colimit.isColimit ((Functor.Elements.π Φ.fiber).op ⋙ F.obj)).isIso_ι_app_of_isTerminal
      _ hInitial.op
  have ht₀ : t₀ = Over.homMk (𝟙 S) (Category.comp_id (𝟙 S)) := by
    apply Over.OverMorphism.ext
    rfl
  change IsIso (Φ.toPresheafFiber T
    (Over.homMk (𝟙 S) (Category.comp_id (𝟙 S))) F.obj)
  rw [← ht₀]
  exact hGerm


/-- Over a separably closed field, invertibility on the actual module of
global sections detects invertibility of an arbitrary module-sheaf morphism. -/
theorem etaleModuleHom_isIso_of_globalSections_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    (Λ : Type u) [CommRing Λ]
    {F G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)}
    (η : F ⟶ G) [IsIso (η.hom.app (op (Scheme.Etale.mk (𝟙 _))))] : IsIso η := by
  let S : Scheme.{u} := Spec (CommRingCat.of k)
  let Φ := Scheme.pointSmallEtale (𝟙 S)
  let T : S.Etale := Scheme.Etale.mk (𝟙 S)
  let v : Φ.fiber.obj T := Over.homMk (𝟙 S) (Category.comp_id (𝟙 S))
  let γF := etaleGlobalSectionsGerm (𝟙 S) Λ F
  let γG := etaleGlobalSectionsGerm (𝟙 S) Λ G
  have hγF : IsIso γF := etaleGlobalSectionsGerm_identity_isIso k Λ F
  have hγG : IsIso γG := etaleGlobalSectionsGerm_identity_isIso k Λ G
  have hη : IsIso (η.hom.app (op T)) :=
    inferInstanceAs (IsIso (η.hom.app
      (op (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of k)))))))
  have hn : γF ≫ Φ.presheafFiber.map η.hom = η.hom.app (op T) ≫ γG :=
    Φ.toPresheafFiber_naturality η.hom T v
  have : IsIso (γF ≫ Φ.presheafFiber.map η.hom) :=
    hn.symm ▸ IsIso.comp_isIso' hη hγG
  have hStalk : IsIso (Φ.sheafFiber.map η) := by
    change IsIso (Φ.presheafFiber.map η.hom)
    exact IsIso.of_isIso_comp_left γF _
  let s : ∀ _ : PUnit.{u + 1}, Spec (CommRingCat.of k) ⟶ S := fun _ => 𝟙 S
  have hcover : ⋃ i : PUnit.{u + 1}, Set.range (s i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨PUnit.unit, x, rfl⟩
  have hpoints := Scheme.isConservative_pointSmallEtale s hcover
  apply ((hpoints.jointlyReflectIsomorphisms (ModuleCat.{u} Λ)).isIso_iff η).mpr
  rintro ⟨_, ⟨i⟩⟩
  exact hStalk

end EtaleCohomology

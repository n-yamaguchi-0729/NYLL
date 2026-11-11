/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Yoneda

/-!
# The actual identity geometric stalk over a separably closed field

The identity geometric point is corepresented by the identity étale object.
Consequently its actual global-section germ is an isomorphism, for arbitrary
coefficient categories with the required colimits, by the terminal-object
calculation of the defining colimit.
-/

@[expose] public section

noncomputable section

universe u vA uA vF

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The literal global-section germ at the identity geometric point,
for any coefficient category with small colimits. -/
def etaleIdentityGlobalSectionsGerm
    (k : Type u) [Field k] [IsSepClosed k]
    (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A]
    (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology A) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of k))))) ⟶
      (Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of k)))).sheafFiber.obj F :=
  (Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of k)))).toPresheafFiber
    (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of k))))
    (Over.homMk (𝟙 (Spec (CommRingCat.of k))) (Category.comp_id _)) F.obj

/-- Corepresentability of the identity point identifies the actual global
sections with the stalk, independently of the coefficient category. -/
theorem etaleIdentityGlobalSectionsGerm_isIso
    (k : Type u) [Field k] [IsSepClosed k]
    (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A]
    (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology A) :
    IsIso (etaleIdentityGlobalSectionsGerm k A F) := by
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

/-- Over a separably closed field, global sections detect isomorphisms
for any concrete coefficient category detected by its underlying sets. -/
theorem etaleHom_isIso_of_globalSections_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A]
    {FC : A → A → Type vF} {CC : A → Type u}
    [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{u} A FC] [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u, u} (forget A)]
    [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose (forget A)]
    {F G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology A}
    (η : F ⟶ G) [IsIso (η.hom.app (op (Scheme.Etale.mk (𝟙 _))))] : IsIso η := by
  let S : Scheme.{u} := Spec (CommRingCat.of k)
  let Φ := Scheme.pointSmallEtale (𝟙 S)
  let T : S.Etale := Scheme.Etale.mk (𝟙 S)
  let v : Φ.fiber.obj T := Over.homMk (𝟙 S) (Category.comp_id (𝟙 S))
  let γF := etaleIdentityGlobalSectionsGerm k A F
  let γG := etaleIdentityGlobalSectionsGerm k A G
  have hγF : IsIso γF := etaleIdentityGlobalSectionsGerm_isIso k A F
  have hγG : IsIso γG := etaleIdentityGlobalSectionsGerm_isIso k A G
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
  apply ((hpoints.jointlyReflectIsomorphisms A).isIso_iff η).mpr
  rintro ⟨_, ⟨i⟩⟩
  exact hStalk

/-- The original module-valued global-section germ is the generic identity germ. -/
theorem etaleGlobalSectionsGerm_identity_isIso
    (k : Type u) [Field k] [IsSepClosed k]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso (etaleGlobalSectionsGerm (𝟙 (Spec (CommRingCat.of k))) Λ F) :=
  etaleIdentityGlobalSectionsGerm_isIso k (ModuleCat.{u} Λ) F

/-- The original module-valued criterion uses the common coefficient-independent proof. -/
theorem etaleModuleHom_isIso_of_globalSections_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    (Λ : Type u) [CommRing Λ]
    {F G : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u} Λ)}
    (η : F ⟶ G) [IsIso (η.hom.app (op (Scheme.Etale.mk (𝟙 _))))] : IsIso η :=
  etaleHom_isIso_of_globalSections_of_isSepClosed k (ModuleCat.{u} Λ) η

end EtaleCohomology

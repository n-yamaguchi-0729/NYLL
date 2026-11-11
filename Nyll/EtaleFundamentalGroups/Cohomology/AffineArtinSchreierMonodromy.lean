/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.AffineArtinSchreierCover
public import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.CategoryTheory.Endomorphism
public import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter

/-!
# Native monodromy of the affine Artin–Schreier cover

Prime-field translations are actual automorphisms of the original root
cover. Its geometric fiber is therefore a torsor under `ZMod p`, and the
original fundamental-group action gives the continuous character.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory Polynomial
open ValuationTheory.DiscreteValuationField

namespace EtaleFundamentalGroups.Cohomology

universe u

variable (R : Type u) [CommRing R] [Nontrivial R]
  (p : ℕ) [Fact p.Prime] [CharP R p] (a : R)

/-- Translation of the actual adjoined root by a prime-field constant. -/
def artinSchreierRootTranslation (c : ZMod p) :
    ArtinSchreierAlgebra R p a →ₐ[R] ArtinSchreierAlgebra R p a := by
  have : CharP (ArtinSchreierAlgebra R p a) p := artinSchreierAlgebra_charP R p a
  let z : R := (ZMod.castHom (dvd_refl p) R) c
  have hz : z ^ p = z := by
    dsimp only [z]
    rw [← map_pow, ZMod.pow_card]
  exact AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (AdjoinRoot.root _ + algebraMap R _ z) (by
      change (X ^ p - X - C a : Polynomial R).eval₂
        (algebraMap R (ArtinSchreierAlgebra R p a))
          (AdjoinRoot.root (artinSchreierPolynomial p a) + algebraMap R _ z) = 0
      rw [eval₂_sub, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
        add_pow_char, ← map_pow, hz]
      have h := artinSchreierAlgebra_root R p a
      linear_combination h)

theorem artinSchreierRootTranslation_root (c : ZMod p) :
    artinSchreierRootTranslation R p a c (AdjoinRoot.root _) =
      AdjoinRoot.root _ + algebraMap R _ ((ZMod.castHom (dvd_refl p) R) c) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem artinSchreierRootTranslation_zero :
    artinSchreierRootTranslation R p a 0 = AlgHom.id R _ := by
  apply AdjoinRoot.algHom_ext
  rw [artinSchreierRootTranslation_root, map_zero, map_zero, add_zero]
  rfl

theorem artinSchreierRootTranslation_add (c d : ZMod p) :
    artinSchreierRootTranslation R p a (c + d) =
      (artinSchreierRootTranslation R p a c).comp
        (artinSchreierRootTranslation R p a d) := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, artinSchreierRootTranslation_root,
    map_add, AlgHom.commutes, add_assoc]

/-- Translation by a prime-field element is invertible, with inverse
translation by its negative. -/
def artinSchreierRootTranslationEquiv (c : ZMod p) :
    ArtinSchreierAlgebra R p a ≃ₐ[R] ArtinSchreierAlgebra R p a :=
  AlgEquiv.ofAlgHom (artinSchreierRootTranslation R p a c)
    (artinSchreierRootTranslation R p a (-c))
    (by rw [← artinSchreierRootTranslation_add, add_neg_cancel,
      artinSchreierRootTranslation_zero])
    (by rw [← artinSchreierRootTranslation_add, neg_add_cancel,
      artinSchreierRootTranslation_zero])

/-- Prime-field translation as an automorphism of the original finite
étale cover, without a connectedness condition. -/
def artinSchreierCoverTranslation (c : ZMod p) : Aut (artinSchreierCover R p a) :=
  Aut.of <| MorphismProperty.Over.isoMk
    (Scheme.Spec.mapIso (artinSchreierRootTranslationEquiv R p a c).toRingEquiv.toCommRingCatIso.op)
    (by
      change Spec.map (CommRingCat.ofHom (artinSchreierRootTranslation R p a c).toRingHom) ≫
        Spec.algebraMap R (ArtinSchreierAlgebra R p a) = _
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      exact RingHom.ext fun r => (artinSchreierRootTranslation R p a c).commutes r)

/-- Prime-field translations form a group of automorphisms of the original
Artin–Schreier cover. -/
def artinSchreierCoverTranslationHom :
    Multiplicative (ZMod p) →* Aut (artinSchreierCover R p a) where
  toFun c := artinSchreierCoverTranslation R p a c.toAdd
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply MorphismProperty.Comma.Hom.ext'
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (artinSchreierRootTranslation R p a 0).toRingHom) = _
    rw [artinSchreierRootTranslation_zero]
    exact Scheme.Spec.map_id _
  map_mul' c d := by
    apply Aut.ext
    apply Iso.ext
    apply MorphismProperty.Comma.Hom.ext'
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom
      (artinSchreierRootTranslation R p a (c.toAdd + d.toAdd)).toRingHom) =
        Spec.map (CommRingCat.ofHom (artinSchreierRootTranslation R p a d.toAdd).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (artinSchreierRootTranslation R p a c.toAdd).toRingHom)
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      ((congrArg (artinSchreierRootTranslation R p a) (add_comm c.toAdd d.toAdd)).trans
        (artinSchreierRootTranslation_add R p a d.toAdd c.toAdd))

variable {Ω : Type u} [Field Ω] [Algebra R Ω] [CharP Ω p] [IsSepClosed Ω]

/-- The action is induced by the actual finite-cover automorphisms. -/
@[instance_reducible]
def artinSchreierFiberAction :
    MulAction (Multiplicative (ZMod p))
      ((FiniteEtale.fiber (Spec.algebraMap R Ω)).obj (artinSchreierCover R p a)) :=
  MulAction.compHom _ (artinSchreierCoverTranslationHom R p a)

theorem artinSchreierFiberEquivRoots_translation
    (c : Multiplicative (ZMod p))
    (x : (FiniteEtale.fiber (Spec.algebraMap R Ω)).obj (artinSchreierCover R p a)) :
    let _ := artinSchreierFiberAction R p a (Ω := Ω)
    (artinSchreierFiberEquivRoots R p a (c • x)).1 =
      (artinSchreierFiberEquivRoots R p a x).1 +
        (ZMod.castHom (dvd_refl p) Ω) c.toAdd := by
  intro sharedOwner1
  let W := artinSchreierCover R p a
  let ξ := Spec.algebraMap R Ω
  let σ := artinSchreierCoverTranslation R p a c.toAdd
  have hn : (FiniteEtale.fiberObjEquivHom ξ W
      ((FiniteEtale.fiber ξ).map σ.asIso.hom x)).left =
        (FiniteEtale.fiberObjEquivHom ξ W x).left ≫ σ.asIso.hom.left :=
    (congrArg (fun f : Over.mk ξ ⟶ W.toComma => f.left)
      (FiniteEtale.fiberObjEquivHom_naturality ξ σ.asIso.hom x)).symm
  let f := (FiniteEtale.fiberObjEquivHom ξ W x).left
  have hpre : Spec.preimage
      (FiniteEtale.fiberObjEquivHom ξ W ((FiniteEtale.fiber ξ).map σ.asIso.hom x)).left =
        CommRingCat.ofHom (artinSchreierRootTranslation R p a c.toAdd).toRingHom ≫
          Spec.preimage f :=
    (congrArg Spec.preimage hn).trans
      ((Spec.preimage_comp f σ.asIso.hom.left).trans
        (congrArg (fun g => g ≫ Spec.preimage f)
          (Spec.preimage_map _)))
  change (Spec.preimage
    (FiniteEtale.fiberObjEquivHom ξ W ((FiniteEtale.fiber ξ).map σ.asIso.hom x)).left)
      (AdjoinRoot.root _) = _
  have heval := ConcreteCategory.congr_hom hpre (AdjoinRoot.root _)
  refine heval.trans ?_
  change (Spec.preimage f).hom
    (artinSchreierRootTranslation R p a c.toAdd (AdjoinRoot.root _)) = _
  rw [artinSchreierRootTranslation_root, map_add]
  congr 1
  simp only [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]

theorem artinSchreierFiberAction_existsUnique
    (x y : (FiniteEtale.fiber (Spec.algebraMap R Ω)).obj (artinSchreierCover R p a)) :
    let _ := artinSchreierFiberAction R p a (Ω := Ω)
    ∃! c : Multiplicative (ZMod p), c • x = y := by
  intro sharedOwner1
  let e := artinSchreierFiberEquivRoots R p a (Ω := Ω)
  have hdiff : ((e y).1 - (e x).1) ^ p = (e y).1 - (e x).1 := by
    rw [sub_pow_char]
    have hx := (e x).2
    have hy := (e y).2
    linear_combination hy - hx
  obtain ⟨c, hc⟩ := ArtinSchreierTheory.exists_zmod_of_pow_eq p Ω hdiff
  have hs : (e x).1 + (ZMod.castHom (dvd_refl p) Ω) c = (e y).1 := by
    rw [hc]
    ring
  refine ⟨Multiplicative.ofAdd c, e.injective (Subtype.ext
    ((artinSchreierFiberEquivRoots_translation R p a _ x).trans hs)), ?_⟩
  intro d hd
  change d.toAdd = c
  apply (ZMod.castHom (dvd_refl p) Ω).injective
  apply add_left_cancel (a := (e x).1)
  exact ((artinSchreierFiberEquivRoots_translation R p a d x).symm.trans
    (congrArg (fun z => (e z).1) hd)).trans hs.symm

/-- The native fiber is a torsor for the original translation maps. -/
@[instance_reducible]
def artinSchreierFiberTorsor :
    Torsor (Multiplicative (ZMod p))
      ((FiniteEtale.fiber (Spec.algebraMap R Ω)).obj (artinSchreierCover R p a)) := by
  let act := artinSchreierFiberAction R p a (Ω := Ω)
  let d (x y : (FiniteEtale.fiber (Spec.algebraMap R Ω)).obj
      (artinSchreierCover R p a)) : Multiplicative (ZMod p) :=
    Classical.choose (artinSchreierFiberAction_existsUnique R p a y x).exists
  have hd (x y : (FiniteEtale.fiber (Spec.algebraMap R Ω)).obj
      (artinSchreierCover R p a)) : d x y • y = x :=
    Classical.choose_spec (artinSchreierFiberAction_existsUnique R p a y x).exists
  have hn : Nonempty ((FiniteEtale.fiber (Spec.algebraMap R Ω)).obj
      (artinSchreierCover R p a)) := by
    obtain ⟨β, hβ⟩ := ArtinSchreierTheory.exists_root p Ω (algebraMap R Ω a)
    exact ⟨(artinSchreierFiberEquivRoots R p a).symm ⟨β, hβ⟩⟩
  exact
    { toMulAction := act
      sdiv := d
      nonempty := hn
      sdiv_smul' := hd
      smul_sdiv' := fun c x =>
        (artinSchreierFiberAction_existsUnique R p a x (c • x)).unique
          (hd (c • x) x) rfl }

omit [IsSepClosed Ω] [CharP Ω p] in
theorem artinSchreierFiberAction_commutes :
    let _ := artinSchreierFiberAction R p a (Ω := Ω)
    SMulCommClass (Aut (FiniteEtale.fiber (Spec.algebraMap R Ω)))
      (Multiplicative (ZMod p))
      ((FiniteEtale.fiber (Spec.algebraMap R Ω)).obj (artinSchreierCover R p a)) := by
  intro sharedOwner1
  constructor
  intro γ c x
  exact ConcreteCategory.congr_hom
    (γ.asIso.hom.naturality (artinSchreierCoverTranslation R p a c.toAdd).asIso.hom) x

/-- The character of an arbitrary affine coefficient is the continuous
displacement of the original fundamental-group action on its actual cover. -/
def affineArtinSchreierCharacter :
    Aut (FiniteEtale.fiber (Spec.algebraMap R Ω)) →ₜ* Multiplicative (ZMod p) := by
  let _ := artinSchreierFiberTorsor R p a (Ω := Ω)
  let _ := artinSchreierFiberAction_commutes R p a (Ω := Ω)
  exact torsorCharacter (Classical.choice inferInstance :
    (FiniteEtale.fiber (Spec.algebraMap R Ω)).obj (artinSchreierCover R p a))

/-- The character has the expected positive root-difference coordinate,
at every point of the original geometric fiber. -/
theorem affineArtinSchreierCharacter_cast
    (x : (FiniteEtale.fiber (Spec.algebraMap R Ω)).obj (artinSchreierCover R p a))
    (γ : Aut (FiniteEtale.fiber (Spec.algebraMap R Ω))) :
    (ZMod.castHom (dvd_refl p) Ω)
        (affineArtinSchreierCharacter R p a (Ω := Ω) γ).toAdd =
      (artinSchreierFiberEquivRoots R p a (γ • x)).1 -
        (artinSchreierFiberEquivRoots R p a x).1 := by
  let _ := artinSchreierFiberTorsor R p a (Ω := Ω)
  let _ := artinSchreierFiberAction_commutes R p a (Ω := Ω)
  have hchar : affineArtinSchreierCharacter R p a (Ω := Ω) = torsorCharacter x :=
    torsorCharacter_eq _ x
  rw [hchar]
  change (ZMod.castHom (dvd_refl p) Ω) (((γ • x) /ₛ x : Multiplicative (ZMod p)).toAdd) = _
  have h :
      (artinSchreierFiberEquivRoots R p a (((γ • x) /ₛ x) • x)).1 =
        (artinSchreierFiberEquivRoots R p a x).1 +
          (ZMod.castHom (dvd_refl p) Ω) (((γ • x) /ₛ x).toAdd) :=
    artinSchreierFiberEquivRoots_translation R p a ((γ • x) /ₛ x) x
  rw [sdiv_smul] at h
  exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans h.symm)

end EtaleFundamentalGroups.Cohomology

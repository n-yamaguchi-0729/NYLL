/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientSchemePresheaf
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroups
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # The vector group and its actual additive points on every test scheme -/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupSchemes

open SchemeTheory.Affine.ScalarQuotientSchemePresheaf

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- A coefficient map acts additively on vector coordinates. -/
def vectorMap (n : ℕ) (g : S →ₐ[R] T) :
    Multiplicative (Fin n → S) →* Multiplicative (Fin n → T) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun x i => g (x i)
      map_zero' := by funext i; exact map_zero g
      map_add' := fun x y => by funext i; exact map_add g (x i) (y i) }

/-- The original additive group of coordinate tuples as an algebra functor. -/
def vectorFunctor (R : Type u) [CommRing R] (n : ℕ) : CommAlgCat.{u} R ⥤ CommGrpCat.{u} where
  obj S := CommGrpCat.of (Multiplicative (Fin n → S))
  map g := CommGrpCat.ofHom (vectorMap n g.hom)
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- The vector group functor on all scheme tests, including nonaffine ones. -/
def vectorPresheaf (R : Type u) [CommRing R] (n : ℕ) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u} :=
  (algΓ (CommRingCat.of R)).op ⋙
    (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ vectorFunctor R n

/-- The affine polynomial scheme underlying the vector group. -/
def vectorObject (R : Type u) [CommRing R] (n : ℕ) : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (MvPolynomial (Fin n) R)))

/-- Polynomial maps are the actual additive coordinate tuples. -/
def vectorPolynomialEquiv (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :
    (MvPolynomial (Fin n) R →ₐ[R] S) ≃ Multiplicative (Fin n → S) where
  toFun p := Multiplicative.ofAdd (fun i => p (MvPolynomial.X i))
  invFun x := MvPolynomial.aeval (Multiplicative.toAdd x)
  left_inv p := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ i
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    exact MvPolynomial.aeval_X (Multiplicative.toAdd x) i

/-- The vector functor is represented by its actual affine polynomial spectrum. -/
def vectorRepresentable (R : Type u) [CommRing R] (n : ℕ) :
    (vectorPresheaf R n ⋙ forget CommGrpCat).RepresentableBy (vectorObject R n) where
  homEquiv {T} :=
    (affinePointEquiv (CommAlgCat.of R (MvPolynomial (Fin n) R)) T).symm.trans
      (vectorPolynomialEquiv R (sectionsAlgebra R T) n)
  homEquiv_comp {T T'} f g := by
    apply Multiplicative.toAdd.injective
    funext i
    change ((affinePointEquiv (CommAlgCat.of R (MvPolynomial (Fin n) R)) T).symm
      (f ≫ g)) (MvPolynomial.X i) =
      sectionsMap f (((affinePointEquiv
        (CommAlgCat.of R (MvPolynomial (Fin n) R)) T').symm g) (MvPolynomial.X i))
    exact congrArg (fun p : MvPolynomial (Fin n) R →ₐ[R] sectionsAlgebra R T =>
      p (MvPolynomial.X i))
      (affinePointEquiv_symm_comp (CommAlgCat.of R (MvPolynomial (Fin n) R)) f g)

/-- The actual commutative vector group of rank `n`. -/
def vectorGroup (R : Type u) [CommRing R] (n : ℕ) : CommGrp (Over (Spec (CommRingCat.of R))) :=
  SchemeTheory.RepresentedGroups.groupObject (vectorPresheaf R n) (vectorRepresentable R n)

/-- Actual vector-group points are tuples of global sections, with addition as group law. -/
def vectorGroupPointEquiv (R : Type u) [CommRing R] (n : ℕ)
    (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (vectorGroup R n).X) ≃* Multiplicative (Fin n → sectionsAlgebra R T) :=
  SchemeTheory.RepresentedGroups.pointEquiv (vectorPresheaf R n) (vectorRepresentable R n) T

/-- The actual point classification is natural under every map of test schemes. -/
theorem vectorGroupPointEquiv_naturality (R : Type u) [CommRing R] (n : ℕ)
    {T T' : Over (Spec (CommRingCat.of R))} (f : T ⟶ T')
    (x : T' ⟶ (vectorGroup R n).X) :
    vectorGroupPointEquiv R n T (f ≫ x) =
      vectorMap n (sectionsMap f) (vectorGroupPointEquiv R n T' x) :=
  (vectorRepresentable R n).homEquiv_comp f x

instance vectorGroup_isAffine (R : Type u) [CommRing R] (n : ℕ) :
    IsAffine (vectorGroup R n).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) R))))

instance vectorGroup_smooth (R : Type u) [CommRing R] (n : ℕ) :
    Smooth (vectorGroup R n).X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.GroupSchemes

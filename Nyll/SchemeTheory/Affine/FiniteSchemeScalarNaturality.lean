/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeScalarQuotient

/-! Naturality of actual finite-scheme scalar classes in the affine test algebra. -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace SchemeTheory.Affine.FiniteScheme

variable {K A B : Type u} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] {Z : Scheme.{u}}

/-- The structure map of a coefficient spectrum. -/
abbrev coefficientMap (A : Type u) [CommRing A] [Algebra K A] :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K A))

theorem coefficientMap_naturality (g : A →ₐ[K] B) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ coefficientMap (K := K) A =
      coefficientMap (K := K) B := by
  rw [coefficientMap, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext g.comp_algebraMap)

variable (q : Z ⟶ Spec (CommRingCat.of K))

/-- The actual scalar map to sections on the base-changed finite scheme. -/
def coefficientScalarMap (A : Type u) [CommRing A] [Algebra K A] :
    A →+* Γ(pullback q (coefficientMap (K := K) A), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (pullback.snd q (coefficientMap (K := K) A)).appTop).hom

/-- The actual morphism between the two finite base-changed schemes. -/
def coefficientPullbackMap (g : A →ₐ[K] B) :
    pullback q (coefficientMap (K := K) B) ⟶ pullback q (coefficientMap (K := K) A) :=
  pullback.lift (pullback.fst q _) (pullback.snd q _ ≫ Spec.map (CommRingCat.ofHom g.toRingHom))
    (by rw [Category.assoc, coefficientMap_naturality]; exact pullback.condition)

@[reassoc] theorem coefficientPullbackMap_fst (g : A →ₐ[K] B) :
    coefficientPullbackMap q g ≫ pullback.fst q (coefficientMap (K := K) A) =
      pullback.fst q (coefficientMap (K := K) B) := pullback.lift_fst _ _ _

@[reassoc] theorem coefficientPullbackMap_snd (g : A →ₐ[K] B) :
    coefficientPullbackMap q g ≫ pullback.snd q (coefficientMap (K := K) A) =
      pullback.snd q (coefficientMap (K := K) B) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) :=
  pullback.lift_snd _ _ _

theorem coefficientPullbackMap_source (g : A →ₐ[K] B) (x : Γ(Z, ⊤)) :
    (coefficientPullbackMap q g).appTop
        ((pullback.fst q (coefficientMap (K := K) A)).appTop x) =
      (pullback.fst q (coefficientMap (K := K) B)).appTop x :=
  congrArg (fun f : Γ(Z, ⊤) ⟶ Γ(pullback q (coefficientMap (K := K) B), ⊤) => f x)
    (congrArg Scheme.Hom.appTop (coefficientPullbackMap_fst q g))

theorem coefficientPullbackMap_scalar (g : A →ₐ[K] B) (a : A) :
    (coefficientPullbackMap q g).appTop
        (coefficientScalarMap q A a) = coefficientScalarMap q B (g a) := by
  have hs := congrArg Scheme.Hom.appTop (coefficientPullbackMap_snd q g)
  simp only [Scheme.Hom.comp_appTop] at hs
  have he : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd q (coefficientMap (K := K) A)).appTop ≫
        (coefficientPullbackMap q g).appTop =
      CommRingCat.ofHom g.toRingHom ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (pullback.snd q (coefficientMap (K := K) B)).appTop := by
    rw [hs, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact congrArg (fun f : CommRingCat.of A ⟶
    Γ(pullback q (coefficientMap (K := K) B), ⊤) => f a) he

variable [IsFinite q]

theorem coordinateAlgebraBaseChangeEquiv_tmul (a : A) (x : coordinateAlgebra q) :
    coordinateAlgebraBaseChangeEquiv (A := A) q (a ⊗ₜ[K] x) =
      coefficientScalarMap q A a * (pullback.fst q (coefficientMap (K := K) A)).appTop x := by
  have ht : a ⊗ₜ[K] x =
      algebraMap A (A ⊗[K] coordinateAlgebra q) a * (1 ⊗ₜ[K] x) := by
    change a ⊗ₜ[K] x = (a ⊗ₜ[K] 1) * (1 ⊗ₜ[K] x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact ((congrArg (coordinateAlgebraBaseChangeEquiv (A := A) q) ht).trans
    (map_mul (coordinateAlgebraBaseChangeEquiv (A := A) q) _ _)).trans
      (congrArg₂ (fun a b : coordinateAlgebra
        (pullback.snd q (coefficientMap (K := K) A)) => a * b)
        ((coordinateAlgebraBaseChangeEquiv (A := A) q).commutes a)
        (coordinateAlgebraBaseChangeEquiv_one_tmul (A := A) q x))

/-- The tensor-to-sections comparison commutes with the actual geometric map. -/
theorem coordinateAlgebraBaseChangeEquiv_naturality (g : A →ₐ[K] B)
    (x : A ⊗[K] coordinateAlgebra q) :
    coordinateAlgebraBaseChangeEquiv (A := B) q
        (Algebra.TensorProduct.map g (AlgHom.id K (coordinateAlgebra q)) x) =
      (coefficientPullbackMap q g).appTop (coordinateAlgebraBaseChangeEquiv (A := A) q x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add (coefficientPullbackMap q g).appTop.hom
      (coordinateAlgebraBaseChangeEquiv (A := A) q x)
      (coordinateAlgebraBaseChangeEquiv (A := A) q y)).symm
  | tmul a x =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hm := congrArg₂
      (fun a b : Γ(pullback q (coefficientMap (K := K) B), ⊤) => a * b)
      (coefficientPullbackMap_scalar q g a).symm
      (coefficientPullbackMap_source q g x).symm
    have hmul := (map_mul (coefficientPullbackMap q g).appTop.hom
      (coefficientScalarMap q A a)
      ((pullback.fst q (coefficientMap (K := K) A)).appTop x)).symm
    have ht := congrArg (coefficientPullbackMap q g).appTop
      (coordinateAlgebraBaseChangeEquiv_tmul q a x).symm
    exact (coordinateAlgebraBaseChangeEquiv_tmul q (g a) x).trans
      (hm.trans (hmul.trans ht))

/-- The actual geometric map on unit classes modulo parameter-spectrum units. -/
def baseChangedScalarQuotientMap (g : A →ₐ[K] B) :
    BaseChangedScalarQuotient (A := A) q →* BaseChangedScalarQuotient (A := B) q :=
  QuotientGroup.map _ _ (Units.map (coefficientPullbackMap q g).appTop.hom.toMonoidHom) (by
    rintro a ⟨s, rfl⟩
    refine ⟨Units.map (Spec.map (CommRingCat.ofHom g.toRingHom)).appTop.hom.toMonoidHom s, ?_⟩
    apply Units.ext
    exact (congrArg (fun f : Γ(Spec (CommRingCat.of A), ⊤) ⟶
      Γ(pullback q (coefficientMap (K := K) B), ⊤) => f (s : Γ(Spec (CommRingCat.of A), ⊤)))
        (congrArg Scheme.Hom.appTop (coefficientPullbackMap_snd q g))).symm)

/-- The scalar quotient comparison is natural, with its geometric map fixed explicitly. -/
theorem baseChangedScalarQuotientEquiv_naturality (g : A →ₐ[K] B)
    (x : ScalarQuotientPresheaf.ScalarQuotient
      (R := K) (A := coordinateAlgebra q) (S := A)) :
    baseChangedScalarQuotientEquiv (A := B) q (ScalarQuotientPresheaf.quotientMap g x) =
      baseChangedScalarQuotientMap q g (baseChangedScalarQuotientEquiv (A := A) q x) := by
  refine QuotientGroup.induction_on x fun a => ?_
  change QuotientGroup.mk (Units.mapEquiv
      (coordinateAlgebraBaseChangeEquiv (A := B) q).toMulEquiv
        (ScalarQuotientPresheaf.unitMap g a)) =
    QuotientGroup.mk (Units.map (coefficientPullbackMap q g).appTop.hom.toMonoidHom
      (Units.mapEquiv (coordinateAlgebraBaseChangeEquiv (A := A) q).toMulEquiv a))
  apply congrArg QuotientGroup.mk
  apply Units.ext
  exact coordinateAlgebraBaseChangeEquiv_naturality q g (a : A ⊗[K] coordinateAlgebra q)

end SchemeTheory.Affine.FiniteScheme

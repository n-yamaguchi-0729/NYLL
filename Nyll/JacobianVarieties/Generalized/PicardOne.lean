/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelZeroClass
import Nyll.JacobianVarieties.Generalized.PicardZeroFieldDetection

/-!
# A basepoint-independent geometric degree-one condition

On every algebraically closed field-valued test, a class differs from an
actual point class on the open curve by a modulus Picard-zero class. This
condition uses no chosen ground-field point. An actual ground-field point
identifies it with its tensor translate of Picard-zero; the comparison is
proved from geometric-field detection and the actual Abel difference theorem.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- Degree one is tested by actual point differences on geometric fields, without a basepoint. -/
def modulusPicardOneSubfunctor : Subfunctor (modulusPicardPresheaf c i) where
  obj T := {x : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) |
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (s : Over.mk t ⟶ T.unop),
      ∃ P : Over.mk t ⟶ Over.mk ((modulusComplement i).ι ≫ c),
      let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) →*
          RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
        ((modulusPicardGroupPresheaf c i).map s.op).hom
      let b : RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
        modulusAbelPointClass c i (T := Over.mk t) P
      m x / b ∈ modulusPicardZeroSubgroup c i (Over.mk t)}
  map {T T'} f := by
    intro x hx k _ _ t s
    obtain ⟨P, hP⟩ := hx k t (s ≫ f.unop)
    refine ⟨P, ?_⟩
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i T'.unop.hom) :=
      ((modulusPicardGroupPresheaf c i).map f).hom
    let n : RigidifiedLineBundle.Classes (modulusBaseChange c i T'.unop.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      ((modulusPicardGroupPresheaf c i).map s.op).hom
    let p : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      ((modulusPicardGroupPresheaf c i).map (s ≫ f.unop).op).hom
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      modulusAbelPointClass c i (T := Over.mk t) P
    have hcomp : n (m x) = p x := by
      let x' : (modulusPicardGroupPresheaf c i).obj T := x
      change ((modulusPicardGroupPresheaf c i).map s.op)
        (((modulusPicardGroupPresheaf c i).map f) x') =
          ((modulusPicardGroupPresheaf c i).map (s ≫ f.unop).op) x'
      exact (ConcreteCategory.congr_hom
        ((modulusPicardGroupPresheaf c i).map_comp f s.op) x').symm
    change n (m x) / b ∈ _
    rw [hcomp]
    exact hP

/-- The actual classes satisfying the geometric degree-one condition. -/
def modulusPicardOnePresheaf : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) :=
  (modulusPicardOneSubfunctor c i).toFunctor

/-- The fppf modulus Picard-one sheaf, defined independently of a ground-field point. -/
def modulusPicardOneSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (Type (u + 1))).obj (modulusPicardOnePresheaf c i)

/-- A point outside the modulus identifies the intrinsic condition with its actual translate. -/
theorem modulusPicardOne_iff_translate
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    (T : Over (Spec (CommRingCat.of R)))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom)) :
    x ∈ (modulusPicardOneSubfunctor c i).obj (op T) ↔
      x / modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T ∈
        modulusPicardZeroSubgroup c i T := by
  constructor
  · intro hx
    apply modulusPicardZero_of_fieldRestrictions c i T.hom
    intro k _ _ s
    let S := Over.mk (s ≫ T.hom)
    let f : S ⟶ T := Over.homMk s rfl
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i S.hom) :=
      ((modulusPicardGroupPresheaf c i).map f.op).hom
    have hb : m (modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T) =
        modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) S :=
      modulusGroundClass_naturality c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) f
    change m (x / modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T) ∈ _
    rw [m.map_div, hb]
    obtain ⟨P, hP⟩ := hx k S.hom f
    let bP : RigidifiedLineBundle.Classes (modulusBaseChange c i S.hom) :=
      modulusAbelPointClass c i (T := Over.mk S.hom) P
    change m x / bP ∈ modulusPicardZeroSubgroup c i S at hP
    have hp : bP /
        modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) S ∈
          modulusPicardZeroSubgroup c i S := (modulusAbelZeroClass c i ε P).2
    have hmul := (modulusPicardZeroSubgroup c i S).mul_mem hP hp
    rw [div_mul_div_cancel] at hmul
    exact hmul
  · intro hx k _ _ t s
    let S := Over.mk t
    let p : S ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
      Over.homMk S.hom (Category.comp_id S.hom)
    refine ⟨p ≫ ε, ?_⟩
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      ((modulusPicardGroupPresheaf c i).map s.op).hom
    have hb : m (modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T) =
        modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) S :=
      modulusGroundClass_naturality c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) s
    have hz := (modulusPicardZeroSubfunctor c i).map s.op hx
    change m (x / modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T) ∈
      modulusPicardZeroSubgroup c i S at hz
    rw [m.map_div, hb] at hz
    have hp : modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) S =
        modulusAbelPointClass c i (p ≫ ε) :=
      modulusGroundClass_abel c i ε S
    rw [hp] at hz
    exact hz

/-- The degree-one subfunctor agrees with the point's translate on all tests. -/
theorem modulusPicardOneSubfunctor_eq_translate
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusPicardOneSubfunctor c i =
      modulusPicardTranslateSubfunctor c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) := by
  ext T x
  exact modulusPicardOne_iff_translate c i ε T.unop x

/-- Tensoring with the actual point class identifies zero and intrinsic degree-one classes. -/
def modulusPicardOneTranslationEquiv
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    (T : Over (Spec (CommRingCat.of R))) :
    modulusPicardZeroSubgroup c i T ≃ (modulusPicardOnePresheaf c i).obj (op T) :=
  (modulusPicardTranslationEquiv c i
    (modulusAbelPointClass c i (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T).trans
      (Equiv.subtypeEquivRight (fun x => (modulusPicardOne_iff_translate c i ε T x).symm))

/-- Tensor translation gives an actual presheaf isomorphism onto Picard-one. -/
def modulusPicardOneTranslationIso
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusPicardZeroPresheaf c i ≅ modulusPicardOnePresheaf c i :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (modulusPicardOneTranslationEquiv c i ε T.unop))
    (fun {T T'} f => by
      apply TypeCat.homEquiv.injective
      funext x
      apply Subtype.ext
      change modulusPicardZeroSubgroup c i T.unop at x
      let b := modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε
      let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) →*
          RigidifiedLineBundle.Classes (modulusBaseChange c i T'.unop.hom) :=
        ((modulusPicardGroupPresheaf c i).map f).hom
      have hm : m (modulusGroundClass c i b T.unop) = modulusGroundClass c i b T'.unop :=
        modulusGroundClass_naturality c i b f.unop
      change m x.1 * modulusGroundClass c i b T'.unop =
        m (x.1 * modulusGroundClass c i b T.unop)
      rw [m.map_mul, hm])

/-- The same actual translation identifies the fppf Picard-zero and Picard-one sheaves. -/
def modulusPicardOneTranslationSheafIso
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusPicardZeroSheaf c i ≅ modulusPicardOneSheaf c i :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (Type (u + 1))).mapIso (modulusPicardOneTranslationIso c i ε)

end AlgebraicGeometry.GeneralizedJacobian

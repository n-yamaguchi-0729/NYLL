/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusScalarExtensionAbelClass
import Nyll.JacobianVarieties.Generalized.ModulusScalarExtensionNaturality
import Nyll.JacobianVarieties.Generalized.PicardOneFieldDetection

/-! # Scalar extension preserves the intrinsic degree-one condition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- On every geometric field, scalar extension preserves the intrinsic point-difference test. -/
theorem scalarExtensionClassesEquiv_one_iff_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R'))
    (x : RigidifiedLineBundle.Classes
      (modulusBaseChange (baseChange R c R') (modulusBaseChange c i (specMap R R')) t)) :
    scalarExtensionClassesEquiv c i R' t x ∈
        (modulusPicardOneSubfunctor c i).obj (op (Over.mk (t ≫ specMap R R'))) ↔
      x ∈ (modulusPicardOneSubfunctor (baseChange R c R')
        (modulusBaseChange c i (specMap R R'))).obj (op (Over.mk t)) := by
  let c' := baseChange R c R'
  let i' := modulusBaseChange c i (specMap R R')
  let e : RigidifiedLineBundle.Classes (modulusBaseChange c' i' t) ≃*
      RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) :=
    scalarExtensionClassesEquiv c i R' t
  constructor
  · intro hx
    obtain ⟨P, hP⟩ :=
      (modulusPicardOne_iff_exists_point c i k (t ≫ specMap R R') (e x)).mp hx
    let P' := modulusScalarExtensionPointLift c i R' (T := Over.mk t) P
    let b' : RigidifiedLineBundle.Classes (modulusBaseChange c' i' t) :=
      modulusAbelPointClass c' i' (T := Over.mk t) P'
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) :=
      modulusAbelPointClass c i (T := Over.mk (t ≫ specMap R R')) P
    let b₀ : RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) :=
      modulusAbelPointClass c i (T := Over.mk (t ≫ specMap R R'))
        (modulusScalarExtensionPoint c i R' (T := Over.mk t) P')
    have hb : b₀ = b := congrArg (fun Q =>
      modulusAbelPointClass c i (T := Over.mk (t ≫ specMap R R')) Q)
      (modulusScalarExtensionPoint_lift c i R' (T := Over.mk t) P)
    have hd : e b' / b₀ ∈ modulusPicardZeroSubgroup c i (Over.mk (t ≫ specMap R R')) :=
      scalarExtensionAbelClass_div_mem_zero c i R' (T := Over.mk t) P'
    rw [hb] at hd
    change e x / b ∈ modulusPicardZeroSubgroup c i (Over.mk (t ≫ specMap R R')) at hP
    have hq := (modulusPicardZeroSubgroup c i (Over.mk (t ≫ specMap R R'))).div_mem hP hd
    rw [div_div_div_cancel_right] at hq
    have hz : x / b' ∈ modulusPicardZeroSubgroup c' i' (Over.mk t) :=
      (scalarExtensionClassesEquiv_zero_iff c i R' t (x / b')).mp (by
        change e (x / b') ∈ modulusPicardZeroSubgroup c i (Over.mk (t ≫ specMap R R'))
        rw [e.map_div]
        exact hq)
    exact (modulusPicardOne_iff_translatePoint c' i' P' x).mpr hz
  · intro hx
    obtain ⟨P', hP'⟩ := (modulusPicardOne_iff_exists_point c' i' k t x).mp hx
    let P := modulusScalarExtensionPoint c i R' (T := Over.mk t) P'
    let b' : RigidifiedLineBundle.Classes (modulusBaseChange c' i' t) :=
      modulusAbelPointClass c' i' (T := Over.mk t) P'
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) :=
      modulusAbelPointClass c i (T := Over.mk (t ≫ specMap R R')) P
    have hz : e x / e b' ∈ modulusPicardZeroSubgroup c i (Over.mk (t ≫ specMap R R')) := by
      have h := (scalarExtensionClassesEquiv_zero_iff c i R' t (x / b')).mpr hP'
      change e (x / b') ∈ modulusPicardZeroSubgroup c i (Over.mk (t ≫ specMap R R')) at h
      rw [e.map_div] at h
      exact h
    have hd : e b' / b ∈ modulusPicardZeroSubgroup c i (Over.mk (t ≫ specMap R R')) :=
      scalarExtensionAbelClass_div_mem_zero c i R' (T := Over.mk t) P'
    have hq := (modulusPicardZeroSubgroup c i (Over.mk (t ≫ specMap R R'))).mul_mem hz hd
    rw [div_mul_div_cancel] at hq
    exact (modulusPicardOne_iff_translatePoint c i P (e x)).mpr hq

/-- The actual scalar-extension class map preserves intrinsic degree one on every parameter. -/
theorem scalarExtensionClassesEquiv_one_iff {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R'))
    (x : RigidifiedLineBundle.Classes
      (modulusBaseChange (baseChange R c R') (modulusBaseChange c i (specMap R R')) t)) :
    scalarExtensionClassesEquiv c i R' t x ∈
        (modulusPicardOneSubfunctor c i).obj (op (Over.mk (t ≫ specMap R R'))) ↔
      x ∈ (modulusPicardOneSubfunctor (baseChange R c R')
        (modulusBaseChange c i (specMap R R'))).obj (op (Over.mk t)) := by
  let c' := baseChange R c R'
  let i' := modulusBaseChange c i (specMap R R')
  let e : RigidifiedLineBundle.Classes (modulusBaseChange c' i' t) ≃*
      RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) :=
    scalarExtensionClassesEquiv c i R' t
  constructor
  · intro hx
    apply modulusPicardOne_of_fieldRestrictions c' i' t x
    intro k _ _ s
    let S := Over.mk (s ≫ t)
    let f : S ⟶ Over.mk t := Over.homMk s rfl
    let f₀ := (Over.map (specMap R R')).map f
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c' i' t) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c' i' (s ≫ t)) :=
      ((modulusPicardGroupPresheaf c' i').map f.op).hom
    let m₀ : RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i ((s ≫ t) ≫ specMap R R')) :=
      ((modulusPicardGroupPresheaf c i).map f₀.op).hom
    let e' := scalarExtensionClassesEquiv c i R' (s ≫ t)
    have hy : m₀ (e x) ∈ (modulusPicardOneSubfunctor c i).obj
        (op ((Over.map (specMap R R')).obj S)) :=
      (modulusPicardOneSubfunctor c i).map f₀.op hx
    have hn : e' (m x) = m₀ (e x) := scalarExtensionClassesEquiv_naturality c i R' f x
    apply (scalarExtensionClassesEquiv_one_iff_of_isAlgClosed c i R' k (s ≫ t) (m x)).mp
    change e' (m x) ∈ (modulusPicardOneSubfunctor c i).obj
      (op ((Over.map (specMap R R')).obj S))
    erw [hn]
    exact hy
  · intro hx
    apply modulusPicardOne_of_fieldRestrictions c i (t ≫ specMap R R') (e x)
    intro k _ _ s
    let S := Over.mk (s ≫ t)
    let f : S ⟶ Over.mk t := Over.homMk s rfl
    let f₀ := (Over.map (specMap R R')).map f
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c' i' t) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c' i' (s ≫ t)) :=
      ((modulusPicardGroupPresheaf c' i').map f.op).hom
    let m₀ : RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i ((s ≫ t) ≫ specMap R R')) :=
      ((modulusPicardGroupPresheaf c i).map f₀.op).hom
    let e' := scalarExtensionClassesEquiv c i R' (s ≫ t)
    have hy : m x ∈ (modulusPicardOneSubfunctor c' i').obj (op S) :=
      (modulusPicardOneSubfunctor c' i').map f.op hx
    have hy' := (scalarExtensionClassesEquiv_one_iff_of_isAlgClosed c i R' k (s ≫ t)
      (m x)).mpr hy
    have hn : e' (m x) = m₀ (e x) := scalarExtensionClassesEquiv_naturality c i R' f x
    change e' (m x) ∈ (modulusPicardOneSubfunctor c i).obj
      (op ((Over.map (specMap R R')).obj S)) at hy'
    erw [hn] at hy'
    let a : Over.mk (s ≫ (t ≫ specMap R R')) ⟶ (Over.map (specMap R R')).obj S :=
      Over.homMk (𝟙 (Spec (CommRingCat.of k)))
        ((Category.id_comp _).trans (Category.assoc s t (specMap R R')))
    let q : Over.mk (s ≫ (t ≫ specMap R R')) ⟶ Over.mk (t ≫ specMap R R') :=
      Over.homMk s rfl
    have hcomp : a ≫ f₀ = q := by
      apply Over.OverMorphism.ext
      exact Category.id_comp s
    let mA : RigidifiedLineBundle.Classes (modulusBaseChange c i ((s ≫ t) ≫ specMap R R')) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i (s ≫ (t ≫ specMap R R'))) :=
      ((modulusPicardGroupPresheaf c i).map a.op).hom
    let mQ : RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i (s ≫ (t ≫ specMap R R'))) :=
      ((modulusPicardGroupPresheaf c i).map q.op).hom
    have hz : mA (m₀ (e x)) ∈ (modulusPicardOneSubfunctor c i).obj
        (op (Over.mk (s ≫ (t ≫ specMap R R')))) :=
      (modulusPicardOneSubfunctor c i).map a.op hy'
    have hm : mA (m₀ (e x)) = mQ (e x) := by
      let F := modulusPicardGroupPresheaf c i
      let z : F.obj (op (Over.mk (t ≫ specMap R R'))) := e x
      change F.map a.op (F.map f₀.op z) = F.map q.op z
      exact (ConcreteCategory.congr_hom (F.map_comp f₀.op a.op) z).symm.trans
        (ConcreteCategory.congr_hom
          (congrArg F.map (congrArg Quiver.Hom.op hcomp)) z)
    change mQ (e x) ∈ (modulusPicardOneSubfunctor c i).obj
      (op (Over.mk (s ≫ (t ≫ specMap R R'))))
    erw [← hm]
    exact hz

/-- The scalar-extension equivalence restricts to exactly the intrinsic degree-one classes. -/
def scalarExtensionOneClassesEquiv (T : Over (Spec (CommRingCat.of R'))) :
    (modulusPicardOnePresheaf (baseChange R c R')
      (modulusBaseChange c i (specMap R R'))).obj (op T) ≃
      (modulusPicardOnePresheaf c i).obj (op ((Over.map (specMap R R')).obj T)) where
  toFun x := ⟨scalarExtensionClassesEquiv c i R' T.hom x.val,
    (scalarExtensionClassesEquiv_one_iff c i R' T.hom x.val).mpr x.property⟩
  invFun y := ⟨(scalarExtensionClassesEquiv c i R' T.hom).symm y.val,
    (scalarExtensionClassesEquiv_one_iff c i R' T.hom _).mp (by
      erw [MulEquiv.apply_symm_apply]
      exact y.property)⟩
  left_inv x := Subtype.ext ((scalarExtensionClassesEquiv c i R' T.hom).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((scalarExtensionClassesEquiv c i R' T.hom).apply_symm_apply y.val)

/-- The actual intrinsic degree-one presheaves agree by the same geometric scalar-extension map. -/
def modulusPicardOneScalarExtensionIso :
    modulusPicardOnePresheaf (baseChange R c R') (modulusBaseChange c i (specMap R R')) ≅
      (Over.map (specMap R R')).op ⋙ modulusPicardOnePresheaf c i :=
  NatIso.ofComponents (fun T => Equiv.toIso (scalarExtensionOneClassesEquiv c i R' T.unop))
    (fun {T T'} f => by
      apply TypeCat.homEquiv.injective
      funext x
      apply Subtype.ext
      exact scalarExtensionClassesEquiv_naturality c i R' f.unop x.val)

end AlgebraicGeometry.GeneralizedJacobian

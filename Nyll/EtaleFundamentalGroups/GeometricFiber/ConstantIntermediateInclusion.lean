/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFiberTransport
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
public import Nyll.EtaleFundamentalGroups.GaloisCovers.ConstantBaseChangeCompactification

/-!
# The original selected points under actual constant-field inclusions

Naturality of the very fiber comparison defining the arithmetic marking
identifies the selected points in nested finite constant covers. Their
original lifts therefore commute with the literal finite-cover projection.
The same coefficient projection commutes with the original open immersions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k κ : Type u) [Field k] [Field κ] [Algebra k κ]
  (E F : IntermediateField k κ)
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k F)))]
  (hEF : E ≤ F)

/-- The actual constant-cover morphism induced by the literal inclusion
of the two original finite intermediate fields. -/
def constantIntermediateInclusion :
    originalConstantFieldCover k F ⟶ originalConstantFieldCover k E :=
  MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hEF).toRingHom)) (by
      change Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hEF).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k E)) =
          Spec.map (CommRingCat.ofHom (algebraMap k F))
      rw [← Spec.map_comp]
      rfl)

/-- The actual projection between the two constant pullbacks. -/
def constantIntermediatePullbackMap {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    ((pullback f).obj (originalConstantFieldCover k F)).left ⟶
      ((pullback f).obj (originalConstantFieldCover k E)).left :=
  ((pullback f).map (constantIntermediateInclusion k κ E F hEF)).hom.left

instance constantIntermediatePullbackMap_isFiniteEtale
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsFiniteEtale (constantIntermediatePullbackMap k κ E F hEF f) :=
  inferInstanceAs (IsFiniteEtale
    (((pullback f).map (constantIntermediateInclusion k κ E F hEF)).hom.left))

/-- The projection retains the actual coefficient inclusion. -/
@[reassoc]
theorem constantIntermediatePullbackMap_fst {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    constantIntermediatePullbackMap k κ E F hEF f ≫
        Limits.pullback.fst (originalConstantFieldCover k E).hom f =
      Limits.pullback.fst (originalConstantFieldCover k F).hom f ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hEF).toRingHom) :=
  Limits.pullback.lift_fst _ _ _

/-- The same projection is over the original scheme. -/
@[reassoc]
theorem constantIntermediatePullbackMap_snd {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    constantIntermediatePullbackMap k κ E F hEF f ≫
        ((pullback f).obj (originalConstantFieldCover k E)).hom =
      ((pullback f).obj (originalConstantFieldCover k F)).hom :=
  MorphismProperty.Over.w ((pullback f).map (constantIntermediateInclusion k κ E F hEF))

/-- The actual nested constant projections commute with the actual
coefficient extensions of an open immersion. -/
theorem constantIntermediatePullbackMap_open
    {X U : Scheme.{u}} (c : X ⟶ Spec (.of k)) (j : U ⟶ X) :
    constantBaseChangeOpen k F c j ≫ constantIntermediatePullbackMap k κ E F hEF c =
      constantIntermediatePullbackMap k κ E F hEF (j ≫ c) ≫
        constantBaseChangeOpen k E c j := by
  let uF := constantBaseChangeOpen k F c j
  let uE := constantBaseChangeOpen k E c j
  let rC := constantIntermediatePullbackMap k κ E F hEF c
  let rU := constantIntermediatePullbackMap k κ E F hEF (j ≫ c)
  let qCE := Limits.pullback.fst (originalConstantFieldCover k E).hom c
  let qCF := Limits.pullback.fst (originalConstantFieldCover k F).hom c
  let qUE := Limits.pullback.fst (originalConstantFieldCover k E).hom (j ≫ c)
  let qUF := Limits.pullback.fst (originalConstantFieldCover k F).hom (j ≫ c)
  let s := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hEF).toRingHom)
  have hC : rC ≫ qCE = qCF ≫ s := constantIntermediatePullbackMap_fst k κ E F hEF c
  have hU : rU ≫ qUE = qUF ≫ s :=
    constantIntermediatePullbackMap_fst k κ E F hEF (j ≫ c)
  have hF : uF ≫ qCF = qUF := constantBaseChangeOpen_structure k F c j
  have hE : uE ≫ qCE = qUE := constantBaseChangeOpen_structure k E c j
  apply Limits.pullback.hom_ext
  · exact (Category.assoc uF rC qCE).trans
      ((congrArg (fun t => uF ≫ t) hC).trans
        ((Category.assoc uF qCF s).symm.trans
          ((congrArg (fun t => t ≫ s) hF).trans
            (hU.symm.trans ((congrArg (fun t => rU ≫ t) hE.symm).trans
              (Category.assoc rU uE qCE).symm)))))
  · let pCE := ((pullback c).obj (originalConstantFieldCover k E)).hom
    let pCF := ((pullback c).obj (originalConstantFieldCover k F)).hom
    let pUE := ((pullback (j ≫ c)).obj (originalConstantFieldCover k E)).hom
    let pUF := ((pullback (j ≫ c)).obj (originalConstantFieldCover k F)).hom
    have hCs : rC ≫ pCE = pCF := constantIntermediatePullbackMap_snd k κ E F hEF c
    have hUs : rU ≫ pUE = pUF :=
      constantIntermediatePullbackMap_snd k κ E F hEF (j ≫ c)
    have hFs : uF ≫ pCF = pUF ≫ j := constantBaseChangeOpen_original k F c j
    have hEs : uE ≫ pCE = pUE ≫ j := constantBaseChangeOpen_original k E c j
    exact (Category.assoc uF rC pCE).trans
      ((congrArg (fun t => uF ≫ t) hCs).trans
        (hFs.trans ((congrArg (fun t => t ≫ j) hUs.symm).trans
          ((Category.assoc rU pUE j).trans
            ((congrArg (fun t => rU ≫ t) hEs.symm).trans
              (Category.assoc rU uE pCE).symm)))))

variable [IsSepClosed κ]

/-- The literal inclusion points of the original constant covers are
compatible under their literal coefficient inclusion. -/
theorem originalInclusionConstantFiberPoint_inclusion :
    (fib k κ).map (constantIntermediateInclusion k κ E F hEF)
        (originalInclusionConstantFiberPoint k F κ) =
      originalInclusionConstantFiberPoint k E κ := by
  apply (fiberObjEquivHom (ξ k κ) (originalConstantFieldCover k E)).injective
  rw [← fiberObjEquivHom_naturality, originalInclusionConstantFiberPoint_hom,
    originalInclusionConstantFiberPoint_hom]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (algebraMap F κ)) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hEF).toRingHom) =
    Spec.map (CommRingCat.ofHom (algebraMap E κ))
  rw [← Spec.map_comp]
  rfl

variable [IsSepClosure k κ]

omit [IsSepClosure k κ] in
/-- Naturality of the original arithmetic fiber comparison, on the
original fiber elements of the actual finite covers. -/
theorem arithmeticConstantFiberEquiv_naturality
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    {A B : FiniteEtale (Spec (.of k))} (r : A ⟶ B)
    (z : (fiber xi).obj ((pullback f).obj A)) :
    arithmeticConstantFiberEquiv k κ f xi B ((fiber xi).map ((pullback f).map r) z) =
      (fib k κ).map r (arithmeticConstantFiberEquiv k κ f xi A z) := by
  let t := (pullbackFiberIso f xi) ≪≫
    (nonempty_fiber_iso (xi ≫ f) (ξ k κ)).some
  exact ConcreteCategory.congr_hom (t.hom.naturality r) z

omit [IsSepClosure k κ] in
/-- The selected arithmetic fiber points in nested original constant
covers are compatible, without choosing another fiber comparison. -/
theorem arithmeticConstantFieldFiberPoint_inclusion
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    (fiber xi).map ((pullback f).map (constantIntermediateInclusion k κ E F hEF))
        (arithmeticConstantFieldFiberPoint k F κ f xi) =
      arithmeticConstantFieldFiberPoint k E κ f xi := by
  apply (arithmeticConstantFiberEquiv k κ f xi (originalConstantFieldCover k E)).injective
  rw [arithmeticConstantFiberEquiv_naturality]
  change (fib k κ).map (constantIntermediateInclusion k κ E F hEF)
      ((arithmeticConstantFiberEquiv k κ f xi (originalConstantFieldCover k F))
        ((arithmeticConstantFiberEquiv k κ f xi (originalConstantFieldCover k F)).symm
          (originalInclusionConstantFiberPoint k F κ))) =
    (arithmeticConstantFiberEquiv k κ f xi (originalConstantFieldCover k E))
      ((arithmeticConstantFiberEquiv k κ f xi (originalConstantFieldCover k E)).symm
        (originalInclusionConstantFiberPoint k E κ))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    originalInclusionConstantFiberPoint_inclusion]

omit [IsSepClosure k κ] in
/-- The selected lifts themselves commute with the actual nested
constant-cover projection. -/
theorem arithmeticConstantFieldLift_inclusion
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    arithmeticConstantFieldLift k F κ f xi ≫ constantIntermediatePullbackMap k κ E F hEF f =
      arithmeticConstantFieldLift k E κ f xi := by
  have h := fiberObjEquivHom_naturality xi
    ((pullback f).map (constantIntermediateInclusion k κ E F hEF))
      (arithmeticConstantFieldFiberPoint k F κ f xi)
  rw [arithmeticConstantFieldFiberPoint_inclusion] at h
  exact congrArg (fun r => r.left) h

end AlgebraicGeometry.FiniteEtale

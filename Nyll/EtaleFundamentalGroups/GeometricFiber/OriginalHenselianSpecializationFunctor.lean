/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperFamilyFiberComparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperCompletionColimitSpecializationFunctor
import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionGeometricLift

/-!
# Cover specialization for original proper henselian families

Fix one actual geometric lift to the constructed completion colimit,
independently of the family. Its cartesian fiber comparisons and the
proved proper comparison over that colimit construct specialization
between the original fibers. Recovery retains covers on the original
total space, and morphisms of original families give natural isomorphisms.
The final endpoint supplies the geometric lift from faithful flatness.
No equivalence over the original henselian total space is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale.CompletionColimitFamily

open HenselianNoetherianImageStages

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]

local notation "C₀" => completionColimit R A
local notation "q₀" => Spec.map (completionBaseMap R A)

section GenericComparison

variable {K L : Type u} [Field K] [Field L]
  (ψ : A →+* K) (β : K →+* L) (α : (completionColimit R A : Type u) →+* L)
  (hα : α.comp (completionBaseMap R A).hom = β.comp ψ)

omit [IsNoetherianRing R] in
include hα in
/-- The supplied actual ring triangle gives the same triangle of geometric points. -/
theorem pointSquare :
    Spec.map (CommRingCat.ofHom α) ≫ q₀ =
      Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom ψ) := by
  have hcat : completionBaseMap R A ≫ CommRingCat.ofHom α =
      CommRingCat.ofHom ψ ≫ CommRingCat.ofHom β := CommRingCat.hom_ext hα
  exact (Spec.map_comp (completionBaseMap R A) (CommRingCat.ofHom α)).symm.trans
    ((congrArg Spec.map hcat).trans
      (Spec.map_comp (CommRingCat.ofHom ψ) (CommRingCat.ofHom β)))

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- The actual fiber comparison uses the original total-space projection. -/
def fiberComparison :
    Limits.pullback (Limits.pullback.snd f q₀) (Spec.map (CommRingCat.ofHom α)) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom ψ)) :=
  properFamilyFiberMapOver (Limits.pullback.snd f q₀) f (Limits.pullback.fst f q₀) q₀
    Limits.pullback.condition.symm (Spec.map (CommRingCat.ofHom α))
    (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom β))
    (pointSquare R A ψ β α hα)

omit [IsNoetherianRing R] in
@[reassoc]
theorem fiberComparison_fst :
    fiberComparison R A ψ β α hα f ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom ψ)) =
      Limits.pullback.fst (Limits.pullback.snd f q₀) (Spec.map (CommRingCat.ofHom α)) ≫
        Limits.pullback.fst f q₀ :=
  properFamilyFiberMapOver_fst _ _ _ _ _ _ _ _ _

omit [IsNoetherianRing R] in
theorem fiberComparison_isPullback :
    IsPullback (fiberComparison R A ψ β α hα f)
      (Limits.pullback.snd (Limits.pullback.snd f q₀) (Spec.map (CommRingCat.ofHom α)))
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) (Spec.map (CommRingCat.ofHom β)) :=
  properFamilyFiberMapOver_isPullback _ _ _ _ _ _ _ _ _
    (IsPullback.of_hasPullback f q₀)

/-- Its pullback is the actual proper separably closed field-extension equivalence. -/
def fiberEquivalence [IsProper f] [IsSepClosed K] [IsSepClosed L] :
    FiniteEtale (Limits.pullback f (Spec.map (CommRingCat.ofHom ψ))) ≌
      FiniteEtale (Limits.pullback (Limits.pullback.snd f q₀)
        (Spec.map (CommRingCat.ofHom α))) := by
  have : (pullback (fiberComparison R A ψ β α hα f)).IsEquivalence :=
    pullback_isEquivalence_of_isProper_of_isSepClosed_field_square K L β
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))
      (fiberComparison R A ψ β α hα f)
      (Limits.pullback.snd (Limits.pullback.snd f q₀) (Spec.map (CommRingCat.ofHom α)))
      (fiberComparison_isPullback R A ψ β α hα f)
  exact (pullback (fiberComparison R A ψ β α hα f)).asEquivalence

/-- The comparison retains the pullback of every cover on the original total space. -/
def fiberComparison_pullbackIso :
    pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom ψ))) ⋙
        pullback (fiberComparison R A ψ β α hα f) ≅
      pullback (Limits.pullback.fst f q₀) ⋙
        pullback (Limits.pullback.fst (Limits.pullback.snd f q₀)
          (Spec.map (CommRingCat.ofHom α))) :=
  (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (fiberComparison R A ψ β α hα f)
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).symm ≪≫
  MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (Limits.pullback.fst (Limits.pullback.snd f q₀) (Spec.map (CommRingCat.ofHom α)))
    (Limits.pullback.fst f q₀) _ (fiberComparison_fst R A ψ β α hα f)

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of A))
  (a : X ⟶ Y) (ha : a ≫ g = f)

omit [IsNoetherianRing R] in
theorem fiberComparison_naturality :
    properFamilyFiberMap (Limits.pullback.snd f q₀) (Limits.pullback.snd g q₀)
        (properFamilyFiberMap f g a ha q₀) (properFamilyFiberMap_snd f g a ha q₀)
        (Spec.map (CommRingCat.ofHom α)) ≫ fiberComparison R A ψ β α hα g =
      fiberComparison R A ψ β α hα f ≫
        properFamilyFiberMap f g a ha (Spec.map (CommRingCat.ofHom ψ)) :=
  properFamilyFiberMapOver_baseChange_naturality f g a ha q₀
    (Spec.map (CommRingCat.ofHom α)) (Spec.map (CommRingCat.ofHom ψ))
    (Spec.map (CommRingCat.ofHom β))
    (pointSquare R A ψ β α hα)

/-- Naturality of the actual fiber comparison at the level of finite étale covers. -/
def fiberComparison_naturalityIso :
    pullback (properFamilyFiberMap f g a ha (Spec.map (CommRingCat.ofHom ψ))) ⋙
        pullback (fiberComparison R A ψ β α hα f) ≅
      pullback (fiberComparison R A ψ β α hα g) ⋙
        pullback (properFamilyFiberMap (Limits.pullback.snd f q₀)
          (Limits.pullback.snd g q₀) (properFamilyFiberMap f g a ha q₀)
          (properFamilyFiberMap_snd f g a ha q₀) (Spec.map (CommRingCat.ofHom α))) :=
  (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (fiberComparison R A ψ β α hα f)
    (properFamilyFiberMap f g a ha (Spec.map (CommRingCat.ofHom ψ)))).symm ≪≫
  MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
    (properFamilyFiberMap (Limits.pullback.snd f q₀) (Limits.pullback.snd g q₀)
      (properFamilyFiberMap f g a ha q₀) (properFamilyFiberMap_snd f g a ha q₀)
      (Spec.map (CommRingCat.ofHom α)))
    (fiberComparison R A ψ β α hα g) _
    (fiberComparison_naturality R A ψ β α hα f g a ha).symm

end GenericComparison

section ClosedComparison

variable {k : Type u} [Field k] (o : IsLocalRing.ResidueField A →+* k)

/-- The original closed point lifted using the proved native residue equivalence. -/
def closedLift : C₀ →+* k :=
  (o.comp (completionResidueEquiv R A).toRingHom).comp (IsLocalRing.residue C₀)

theorem closedLift_comp_base :
    (closedLift R A o).comp (completionBaseMap R A).hom =
      (RingHom.id k).comp (o.comp (IsLocalRing.residue A)) := by
  apply RingHom.ext
  intro a
  exact congrArg o (completionResidueEquiv_base_residue R A a)

theorem closedLift_factor :
    Spec.map (CommRingCat.ofHom (closedLift R A o)) =
      Spec.map (CommRingCat.ofHom (o.comp (completionResidueEquiv R A).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue C₀)) :=
  Spec.map_comp (CommRingCat.ofHom (IsLocalRing.residue C₀))
    (CommRingCat.ofHom (o.comp (completionResidueEquiv R A).toRingHom))

end ClosedComparison

section Specialization

variable [IsSepClosed (IsLocalRing.ResidueField A)]
  {K L k : Type u} [Field K] [IsSepClosed K] [Field L] [IsSepClosed L]
  [Field k] [IsSepClosed k]
  (ψ : A →+* K) (β : K →+* L) (α : (completionColimit R A : Type u) →+* L)
  (hα : α.comp (completionBaseMap R A).hom = β.comp ψ)
  (o : IsLocalRing.ResidueField A →+* k)

local notation "s₀" => Spec.map (CommRingCat.ofHom (o.comp (IsLocalRing.residue A)))
local notation "sC" => Spec.map (CommRingCat.ofHom (closedLift R A o))
local notation "η₀" => Spec.map (CommRingCat.ofHom ψ)
local notation "ηC" => Spec.map (CommRingCat.ofHom α)

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- Specialization between the original fibers, using constructed comparisons only. -/
def specializationFunctor : FiniteEtale (Limits.pullback f s₀) ⥤
    FiniteEtale (Limits.pullback f η₀) :=
  (pullback (fiberComparison R A (o.comp (IsLocalRing.residue A)) (RingHom.id k)
      (closedLift R A o) (closedLift_comp_base R A o) f) ⋙
    properCompletionColimitGeometricSpecializationFunctor R A (Limits.pullback.snd f q₀)
      sC (o.comp (completionResidueEquiv R A).toRingHom) (closedLift_factor R A o) ηC) ⋙
    (fiberEquivalence R A ψ β α hα f).inverse

/-- A cover on the original total space recovers its original generic restriction. -/
def specializationFunctor_recovery :
    pullback (Limits.pullback.fst f s₀) ⋙ specializationFunctor R A ψ β α hα o f ≅
      pullback (Limits.pullback.fst f η₀) := by
  let E := fiberEquivalence R A ψ β α hα f
  let J := pullback (Limits.pullback.fst f s₀)
  let H := pullback (Limits.pullback.fst f q₀)
  let M := pullback (fiberComparison R A (o.comp (IsLocalRing.residue A)) (RingHom.id k)
    (closedLift R A o) (closedLift_comp_base R A o) f)
  let N := pullback (Limits.pullback.fst (Limits.pullback.snd f q₀) sC)
  let P := pullback (Limits.pullback.fst (Limits.pullback.snd f q₀) ηC)
  let Q := pullback (Limits.pullback.fst f η₀)
  let F := properCompletionColimitGeometricSpecializationFunctor R A
    (Limits.pullback.snd f q₀) sC (o.comp (completionResidueEquiv R A).toRingHom)
    (closedLift_factor R A o) ηC
  let cs : J ⋙ M ≅ H ⋙ N := fiberComparison_pullbackIso R A
    (o.comp (IsLocalRing.residue A)) (RingHom.id k)
    (closedLift R A o) (closedLift_comp_base R A o) f
  let cη : Q ⋙ E.functor ≅ H ⋙ P := fiberComparison_pullbackIso R A ψ β α hα f
  let r : N ⋙ F ≅ P := properCompletionColimitGeometricSpecializationFunctor_recovery
    R A (Limits.pullback.snd f q₀) sC (o.comp (completionResidueEquiv R A).toRingHom)
    (closedLift_factor R A o) ηC
  change J ⋙ ((M ⋙ F) ⋙ E.inverse) ≅ Q
  exact (Functor.associator J (M ⋙ F) E.inverse).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator J M F).symm E.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight cs F) E.inverse ≪≫
    Functor.isoWhiskerRight (Functor.associator H N F) E.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft H r) E.inverse ≪≫
    Functor.isoWhiskerRight cη.symm E.inverse ≪≫
    Functor.associator Q E.functor E.inverse ≪≫
    Functor.isoWhiskerLeft Q E.unitIso.symm ≪≫ Functor.rightUnitor Q

/-- A morphism of original families commutes with specialization for the
same geometric lift, which was chosen independently of the family. -/
def specializationFunctor_naturality
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of A)) [IsProper g]
    (a : X ⟶ Y) (ha : a ≫ g = f) :
    pullback (properFamilyFiberMap f g a ha s₀) ⋙
        specializationFunctor R A ψ β α hα o f ≅
      specializationFunctor R A ψ β α hα o g ⋙
        pullback (properFamilyFiberMap f g a ha η₀) := by
  let fC := Limits.pullback.snd f q₀
  let gC := Limits.pullback.snd g q₀
  let aC := properFamilyFiberMap f g a ha q₀
  let haC : aC ≫ gC = fC := properFamilyFiberMap_snd f g a ha q₀
  let E := fiberEquivalence R A ψ β α hα f
  let E' := fiberEquivalence R A ψ β α hα g
  let M := pullback (fiberComparison R A (o.comp (IsLocalRing.residue A)) (RingHom.id k)
    (closedLift R A o) (closedLift_comp_base R A o) f)
  let M' := pullback (fiberComparison R A (o.comp (IsLocalRing.residue A)) (RingHom.id k)
    (closedLift R A o) (closedLift_comp_base R A o) g)
  let F := properCompletionColimitGeometricSpecializationFunctor R A fC sC
    (o.comp (completionResidueEquiv R A).toRingHom) (closedLift_factor R A o) ηC
  let F' := properCompletionColimitGeometricSpecializationFunctor R A gC sC
    (o.comp (completionResidueEquiv R A).toRingHom) (closedLift_factor R A o) ηC
  let J := pullback (properFamilyFiberMap f g a ha s₀)
  let J' := pullback (properFamilyFiberMap fC gC aC haC sC)
  let P := pullback (properFamilyFiberMap f g a ha η₀)
  let P' := pullback (properFamilyFiberMap fC gC aC haC ηC)
  let cs : J ⋙ M ≅ M' ⋙ J' := fiberComparison_naturalityIso R A
    (o.comp (IsLocalRing.residue A)) (RingHom.id k)
    (closedLift R A o) (closedLift_comp_base R A o) f g a ha
  let cη : P ⋙ E.functor ≅ E'.functor ⋙ P' :=
    fiberComparison_naturalityIso R A ψ β α hα f g a ha
  let d : (E'.inverse ⋙ P) ⋙ E.functor ≅ P' :=
    Functor.associator E'.inverse P E.functor ≪≫ cη.inverseCompIso (G := E')
  let b : P' ⋙ E.inverse ≅ E'.inverse ⋙ P := (d.isoCompInverse (H := E)).symm
  let n : J' ⋙ F ≅ F' ⋙ P' :=
    properCompletionColimitGeometricSpecializationFunctor_naturality R A fC sC
      (o.comp (completionResidueEquiv R A).toRingHom) (closedLift_factor R A o) ηC
      gC aC haC
  change J ⋙ ((M ⋙ F) ⋙ E.inverse) ≅ ((M' ⋙ F') ⋙ E'.inverse) ⋙ P
  exact (Functor.associator J (M ⋙ F) E.inverse).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator J M F).symm E.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight cs F) E.inverse ≪≫
    Functor.isoWhiskerRight (Functor.associator M' J' F) E.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft M' n) E.inverse ≪≫
    Functor.isoWhiskerRight (Functor.associator M' F' P').symm E.inverse ≪≫
    Functor.associator (M' ⋙ F') P' E.inverse ≪≫
    Functor.isoWhiskerLeft (M' ⋙ F') b ≪≫
    (Functor.associator (M' ⋙ F') E'.inverse P).symm

end Specialization

/-- Faithful flatness supplies one geometric lift for all original proper
families. The constructed specialization functors recover original covers. -/
theorem exists_specializationFunctors
    [IsSepClosed (IsLocalRing.ResidueField A)]
    {K k : Type u} [Field K] [IsSepClosed K] [Field k] [IsSepClosed k]
    (ψ : A →+* K) (o : IsLocalRing.ResidueField A →+* k) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L)
      (β : K →+* L) (α : completionColimit R A →+* L)
      (hα : α.comp (completionBaseMap R A).hom = β.comp ψ),
      ∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)) (_ : IsProper f),
        Nonempty (pullback (Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (o.comp (IsLocalRing.residue A))))) ⋙
          specializationFunctor R A ψ β α hα o f ≅
            pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))) := by
  obtain ⟨L, hL, hLc, β, α, hα⟩ := exists_completionGeometricLift R A ψ
  exact ⟨L, hL, hLc, β, α, hα, fun X f hf =>
    ⟨specializationFunctor_recovery R A ψ β α hα o f⟩⟩

end AlgebraicGeometry.FiniteEtale.CompletionColimitFamily

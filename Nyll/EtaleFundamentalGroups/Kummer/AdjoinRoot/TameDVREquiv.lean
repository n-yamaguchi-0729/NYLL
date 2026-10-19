/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.TameDVR
import Nyll.SchemeTheory.RingTheory.Ramification.LocalRingResidueCharacteristicTransport
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
import Mathlib.Algebra.CharP.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# Tameness under compatible changes of DVR and ambient field

Both the integral closure and its prime residue maps are transported by
the actual ring equivalences. The ramification-index comparison uses the
same images of ideals, not an assumed comparison of valuations or fields.
The characteristic-zero alternative in Stacks Project, Definition
15.113.7 (tag `09E9`) is preserved as well.
-/

noncomputable section

namespace SchemeTheory

universe uR uS uT uU

private theorem ramificationIdx'_baseEquiv
    {R : Type uR} {S : Type uS} {U : Type uU}
    [CommRing R] [CommRing S] [CommRing U] [Algebra R U] [Algebra S U]
    (e : R ≃+* S)
    (h : (algebraMap S U).comp e.toRingHom = algebraMap R U)
    (Q : Ideal U) :
    Ideal.ramificationIdx' (Q.under R) Q = Ideal.ramificationIdx' (Q.under S) Q := by
  have hunder : Q.under R = (Q.under S).comap e.toRingHom := by
    change Q.comap (algebraMap R U) = Q.comap ((algebraMap S U).comp e.toRingHom)
    rw [h]
  have hmap : (Q.under R).map (algebraMap R U) =
      (Q.under S).map (algebraMap S U) := by
    rw [hunder, ← h, ← Ideal.map_map,
      Ideal.map_comap_of_surjective e.toRingHom e.surjective]
  unfold Ideal.ramificationIdx'
  rw [hmap]

private theorem ramificationIdx'_compatibleEquiv
    {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra S U]
    (eBase : R ≃+* S) (eTarget : T ≃+* U)
    (h : eTarget.toRingHom.comp (algebraMap R T) =
      (algebraMap S U).comp eBase.toRingHom) (Q : Ideal U) :
    Ideal.ramificationIdx' ((Q.comap eTarget.toRingHom).under R)
        (Q.comap eTarget.toRingHom) =
      Ideal.ramificationIdx' (Q.under S) Q := by
  let : Algebra R U := ((algebraMap S U).comp eBase.toRingHom).toAlgebra
  let e : T ≃ₐ[R] U :=
    AlgEquiv.ofRingEquiv (f := eTarget) fun r => DFunLike.congr_fun h r
  have hunder : (Q.comap eTarget.toRingHom).under R = Q.under R := by
    change Q.comap (eTarget.toRingHom.comp (algebraMap R T)) =
      Q.comap (algebraMap R U)
    exact congrArg (fun φ : R →+* U => Q.comap φ) h
  rw [hunder]
  exact (Ideal.ramificationIdx'_comap_eq (Q.under R) e Q).trans
    (ramificationIdx'_baseEquiv eBase rfl Q)

private theorem primeTame_of_compatibleEquiv
    {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra S U]
    (eBase : R ≃+* S) (eTarget : T ≃+* U)
    (h : eTarget.toRingHom.comp (algebraMap R T) =
      (algebraMap S U).comp eBase.toRingHom)
    (Q' : Ideal U) [Q'.IsPrime] :
    let Q := Q'.comap eTarget.toRingHom
    let : Algebra (Q.under R).ResidueField Q.ResidueField :=
      (Ideal.ResidueField.map (Q.under R) Q (algebraMap R T) rfl).toAlgebra
    let : Algebra (Q'.under S).ResidueField Q'.ResidueField :=
      (Ideal.ResidueField.map (Q'.under S) Q' (algebraMap S U) rfl).toAlgebra
    Algebra.IsSeparable (Q.under R).ResidueField Q.ResidueField ∧
        IsUnit (Ideal.ramificationIdx' (Q.under R) Q : (Q.under R).ResidueField) →
      Algebra.IsSeparable (Q'.under S).ResidueField Q'.ResidueField ∧
        IsUnit (Ideal.ramificationIdx' (Q'.under S) Q' : (Q'.under S).ResidueField) := by
  intro Q hOldAlgebra hNewAlgebra htame
  let p := Q.under R
  let p' := Q'.under S
  have hp : p = p'.comap eBase.toRingHom := by
    change Q'.comap (eTarget.toRingHom.comp (algebraMap R T)) =
      Q'.comap ((algebraMap S U).comp eBase.toRingHom)
    rw [h]
  let eP : p.ResidueField ≃+* p'.ResidueField :=
    Ideal.residueFieldRingEquiv p p' eBase hp
  let eQ : Q.ResidueField ≃+* Q'.ResidueField :=
    Ideal.residueFieldRingEquiv Q Q' eTarget rfl
  have heP (r : R) : eP (algebraMap R p.ResidueField r) =
      algebraMap S p'.ResidueField (eBase r) :=
    Ideal.ResidueField.map_algebraMap p p' eBase.toRingHom hp r
  have heQ (t : T) : eQ (algebraMap T Q.ResidueField t) =
      algebraMap U Q'.ResidueField (eTarget t) :=
    Ideal.ResidueField.map_algebraMap Q Q' eTarget.toRingHom rfl t
  have hresidue :
      (algebraMap p'.ResidueField Q'.ResidueField).comp eP.toRingHom =
        eQ.toRingHom.comp (algebraMap p.ResidueField Q.ResidueField) := by
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro r
    change Ideal.ResidueField.map p' Q' (algebraMap S U) rfl
        (eP (algebraMap R p.ResidueField r)) =
      eQ (Ideal.ResidueField.map p Q (algebraMap R T) rfl
        (algebraMap R p.ResidueField r))
    rw [heP, Ideal.ResidueField.map_algebraMap,
      Ideal.ResidueField.map_algebraMap, heQ]
    exact congrArg (algebraMap U Q'.ResidueField) (DFunLike.congr_fun h r).symm
  have hseparable : Algebra.IsSeparable p.ResidueField Q.ResidueField := htame.1
  refine ⟨Algebra.IsSeparable.of_equiv_equiv eP eQ hresidue, ?_⟩
  have hunit := htame.2.map eP.toRingHom
  have hindex : Ideal.ramificationIdx' (Q.under R) Q =
      Ideal.ramificationIdx' (Q'.under S) Q' :=
    ramificationIdx'_compatibleEquiv eBase eTarget h Q'
  simpa only [map_natCast, hindex] using hunit

/-- Simultaneously replacing a DVR and its ambient field by compatible
isomorphic rings preserves tameness. The equivalence of the literal
integral closures and all residue-field comparisons are constructed here. -/
theorem isTamelyRamifiedOverDVR_of_compatible_ringEquiv
    {R : Type uR} {S : Type uS} {L : Type uT} {M : Type uU}
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Field L] [Field M] [Algebra R L] [Algebra S M]
    (eBase : R ≃+* S) (eField : L ≃+* M)
    (h : eField.toRingHom.comp (algebraMap R L) =
      (algebraMap S M).comp eBase.toRingHom)
    (htame : IsTamelyRamifiedOverDVR R L) : IsTamelyRamifiedOverDVR S M := by
  rcases htame with hzero | hprimes
  · have : CharP (IsLocalRing.ResidueField R) 0 := ringChar.of_eq hzero
    have : CharP (IsLocalRing.ResidueField S) 0 :=
      residueField_charP_of_ringEquiv eBase 0
    exact Or.inl (ringChar.eq (IsLocalRing.ResidueField S) 0)
  · let : Algebra R (integralClosure S M) :=
      EtaleFundamentalGroups.integralClosureBaseRingAlgebra eBase
    let e : integralClosure R L ≃ₐ[R] integralClosure S M :=
      EtaleFundamentalGroups.integralClosureAlgEquivOfBaseAndAmbientEquiv eBase eField h
    have hclosure : e.toRingHom.comp (algebraMap R (integralClosure R L)) =
        (algebraMap S (integralClosure S M)).comp eBase.toRingHom := by
      exact e.toAlgHom.comp_algebraMap
    apply Or.inr
    intro Q' hQ' hResidueAlgebra
    let Q : Ideal (integralClosure R L) := Q'.comap e.toRingEquiv.toRingHom
    have : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective
      e.toRingEquiv.toRingHom e.surjective
    exact primeTame_of_compatibleEquiv eBase e.toRingEquiv hclosure Q' (hprimes Q)

end SchemeTheory

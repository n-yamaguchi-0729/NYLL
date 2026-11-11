/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.DVRCompletionComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ConnectedComponents
public import Nyll.EtaleFundamentalGroups.GaloisCategories.EquivalenceFunctoriality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Specialization on the original geometric fibres of a DVR family

The actual DVR-completion comparison supplies the geometric-fibre maps
and their finite-etale equivalences. Specialization on the completed
family is transported through those equivalences to the original DVR
fibres. Its path is pushed to the original total space, and the triangle
uses the original fibre projections.

Connectedness of the two specified geometric fibers supplies points and a path.
Geometric connectedness of the whole family is sufficient but unnecessary.
No comparison, completion-independence, or arbitrary-base specialization
is assumed.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

open AlgebraicGeometry.FiniteEtale

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

private theorem conjAut_of_point_transports_eq
    {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x y z : Spec (.of Ω) ⟶ X}
    (hx : x = z) (hy : y = z) (a : π₁ᵉᵗ(x)) (b : π₁ᵉᵗ(y))
    (h : hx ▸ a = hy ▸ b) :
    (eqToIso (congrArg FiniteEtale.fiber (hx.trans hy.symm))).conjAut a = b := by
  subst z
  subst y
  exact h

private theorem fundamentalGroupHom_square
    {T U V X : Scheme.{u}}
    (a : T ⟶ U) (b : U ⟶ X) (c : T ⟶ V) (d : V ⟶ X)
    (h : a ≫ b = c ≫ d) {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ T)
    (hx : (x ≫ a) ≫ b = (x ≫ c) ≫ d) (α : π₁ᵉᵗ(x)) :
    (eqToIso (congrArg FiniteEtale.fiber hx)).conjAut
        (fundamentalGroupHom b (x ≫ a) (fundamentalGroupHom a x α)) =
      fundamentalGroupHom d (x ≫ c) (fundamentalGroupHom c x α) := by
  let hleft : (x ≫ a) ≫ b = x ≫ c ≫ d :=
    (Category.assoc x a b).trans (congrArg (fun k => x ≫ k) h)
  let hright : (x ≫ c) ≫ d = x ≫ c ≫ d := Category.assoc x c d
  exact conjAut_of_point_transports_eq hleft hright _ _
    ((fundamentalGroupHom_comp_of_eq a b (c ≫ d) h.symm x hleft α).trans
      (fundamentalGroupHom_comp_of_eq c d (c ≫ d) rfl x hright α).symm)

private theorem fundamentalGroupEquivalence_apply
    {T U : Scheme.{u}} (q : T ⟶ U) [(FiniteEtale.pullback q).IsEquivalence]
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ T) (a : π₁ᵉᵗ(x)) :
    autEquivOfCompIsoOfEquivalence (FiniteEtale.pullback q) (pullbackFiberIso q x) a =
      fundamentalGroupHom q x a :=
  autEquivOfCompIsoOfEquivalence_apply (FiniteEtale.pullback q) (pullbackFiberIso q x) a

private theorem conjAut_cancel_target
    {C : Type*} [Category C] {A B D E : C}
    (a : A ≅ B) (t : B ≅ D) (c : E ≅ D) (b : Aut A) :
    c.conjAut ((a ≪≫ t ≪≫ c.symm).conjAut b) = t.conjAut (a.conjAut b) := by
  rw [Iso.trans_conjAut, Iso.trans_conjAut]
  exact c.conjAut.apply_symm_apply (t.conjAut (a.conjAut b))

/-- Transport an already constructed specialization through two actual
geometric-fibre comparisons, retaining the original projection triangles
and the induced path on the target total space. -/
theorem transportSpecializationThroughFiberComparisons
    {T U T' U' Y X : Scheme.{u}}
    (qη : T' ⟶ T) (qs : U' ⟶ U) (jη : T' ⟶ Y) (js : U' ⟶ Y)
    (pη : T ⟶ X) (ps : U ⟶ X) (l : Y ⟶ X)
    (hη : qη ≫ pη = jη ≫ l) (hs : qs ≫ ps = js ≫ l)
    [(FiniteEtale.pullback qη).IsEquivalence]
    [(FiniteEtale.pullback qs).IsEquivalence]
    {Ωη Ωs : Type u} [Field Ωη] [Field Ωs]
    (xη : Spec (.of Ωη) ⟶ T') (xs : Spec (.of Ωs) ⟶ U')
    (t : FiniteEtale.fiber (xη ≫ jη) ≅ FiniteEtale.fiber (xs ≫ js))
    (spHat : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs))
    (hhat : ∀ b, fundamentalGroupHom js xs (spHat b) =
      continuousConjAut t (fundamentalGroupHom jη xη b)) :
    ∃ tOld : FiniteEtale.fiber ((xη ≫ qη) ≫ pη) ≅
        FiniteEtale.fiber ((xs ≫ qs) ≫ ps),
      ∃ sp : π₁ᵉᵗ(xη ≫ qη) →ₜ* π₁ᵉᵗ(xs ≫ qs), ∀ α,
        fundamentalGroupHom ps (xs ≫ qs) (sp α) =
          continuousConjAut tOld (fundamentalGroupHom pη (xη ≫ qη) α) := by
  let eη : π₁ᵉᵗ(xη) ≃ₜ* π₁ᵉᵗ(xη ≫ qη) :=
    autEquivOfCompIsoOfEquivalence (FiniteEtale.pullback qη) (pullbackFiberIso qη xη)
  let es : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xs ≫ qs) :=
    autEquivOfCompIsoOfEquivalence (FiniteEtale.pullback qs) (pullbackFiberIso qs xs)
  let sp : π₁ᵉᵗ(xη ≫ qη) →ₜ* π₁ᵉᵗ(xs ≫ qs) :=
    (ContinuousMonoidHom.toContinuousMonoidHom es).comp
      (spHat.comp (ContinuousMonoidHom.toContinuousMonoidHom eη.symm))
  let hηpoint : (xη ≫ qη) ≫ pη = (xη ≫ jη) ≫ l :=
    (Category.assoc xη qη pη).trans
      ((congrArg (fun k => xη ≫ k) hη).trans (Category.assoc xη jη l).symm)
  let hspoint : (xs ≫ qs) ≫ ps = (xs ≫ js) ≫ l :=
    (Category.assoc xs qs ps).trans
      ((congrArg (fun k => xs ≫ k) hs).trans (Category.assoc xs js l).symm)
  let cη : FiniteEtale.fiber ((xη ≫ qη) ≫ pη) ≅
      FiniteEtale.fiber ((xη ≫ jη) ≫ l) :=
    eqToIso (congrArg FiniteEtale.fiber hηpoint)
  let cs : FiniteEtale.fiber ((xs ≫ qs) ≫ ps) ≅
      FiniteEtale.fiber ((xs ≫ js) ≫ l) :=
    eqToIso (congrArg FiniteEtale.fiber hspoint)
  let tl : FiniteEtale.fiber ((xη ≫ jη) ≫ l) ≅
      FiniteEtale.fiber ((xs ≫ js) ≫ l) :=
    (pullbackFiberIso l (xη ≫ jη)).symm ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback l) t ≪≫ pullbackFiberIso l (xs ≫ js)
  let tOld : FiniteEtale.fiber ((xη ≫ qη) ≫ pη) ≅
      FiniteEtale.fiber ((xs ≫ qs) ≫ ps) := cη ≪≫ tl ≪≫ cs.symm
  have hηcomp (b : π₁ᵉᵗ(xη)) :
      cη.conjAut (fundamentalGroupHom pη (xη ≫ qη) (eη b)) =
        fundamentalGroupHom l (xη ≫ jη) (fundamentalGroupHom jη xη b) :=
    (congrArg (fun a => cη.conjAut (fundamentalGroupHom pη (xη ≫ qη) a))
      (fundamentalGroupEquivalence_apply qη xη b)).trans
        (fundamentalGroupHom_square qη pη jη l hη xη hηpoint b)
  have hscomp (b : π₁ᵉᵗ(xs)) :
      cs.conjAut (fundamentalGroupHom ps (xs ≫ qs) (es b)) =
        fundamentalGroupHom l (xs ≫ js) (fundamentalGroupHom js xs b) :=
    (congrArg (fun a => cs.conjAut (fundamentalGroupHom ps (xs ≫ qs) a))
      (fundamentalGroupEquivalence_apply qs xs b)).trans
        (fundamentalGroupHom_square qs ps js l hs xs hspoint b)
  have hpath (b : π₁ᵉᵗ((xη ≫ qη) ≫ pη)) :
      cs.conjAut (tOld.conjAut b) = tl.conjAut (cη.conjAut b) := by
    exact conjAut_cancel_target cη tl cs b
  refine ⟨tOld, sp, ?_⟩
  intro α
  let b : π₁ᵉᵗ(xη) := eη.symm α
  have hb : eη b = α := eη.apply_symm_apply α
  have hηb : cη.conjAut (fundamentalGroupHom pη (xη ≫ qη) α) =
      fundamentalGroupHom l (xη ≫ jη) (fundamentalGroupHom jη xη b) := by
    simpa only [hb] using hηcomp b
  apply cs.conjAut.injective
  change cs.conjAut (fundamentalGroupHom ps (xs ≫ qs) (es (spHat b))) =
    cs.conjAut (tOld.conjAut (fundamentalGroupHom pη (xη ≫ qη) α))
  calc
    _ = fundamentalGroupHom l (xs ≫ js) (fundamentalGroupHom js xs (spHat b)) :=
      hscomp (spHat b)
    _ = fundamentalGroupHom l (xs ≫ js) (t.conjAut (fundamentalGroupHom jη xη b)) :=
      congrArg (fundamentalGroupHom l (xs ≫ js)) (hhat b)
    _ = tl.conjAut (fundamentalGroupHom l (xη ≫ jη) (fundamentalGroupHom jη xη b)) :=
      (fundamentalGroupHom_conjAut l (xη ≫ jη) (xs ≫ js) t
        (fundamentalGroupHom jη xη b)).symm
    _ = tl.conjAut (cη.conjAut (fundamentalGroupHom pη (xη ≫ qη) α)) :=
      congrArg tl.conjAut hηb.symm
    _ = _ := (hpath _).symm

/-- Connectedness of the two specified geometric fibers is enough to
construct specialization by completing the actual DVR family. The field
comparisons transfer connectedness to the completed fibers; the completed
closed-fiber equivalence then supplies connectedness of the total space.
The path and triangle retain the original total space `X`. -/
theorem exists_dvrCompletionSpecialization_of_connectedFibers
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsSepClosed (ResidueField D)]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (p : Spec (.of D) ⟶ S)
    {K k : Type u} [Field K] [IsSepClosed K] [Field k] [IsSepClosed k]
    (η : FractionRing D →+* K) (o : ResidueField D →+* k)
    (hgeneric : ConnectedSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom η) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D))))
      (pullback.fst p f)))
    (hspecial : ConnectedSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom (o.comp (residue D)))) (pullback.fst p f))) :
    let g := pullback.fst p f
    let γ := Spec.map (CommRingCat.ofHom η) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))
    let δ := Spec.map (CommRingCat.ofHom (o.comp (residue D)))
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback γ g) (xs : Spec (.of Ωs) ⟶ pullback δ g)
      (t : FiniteEtale.fiber (xη ≫ (pullback.snd γ g ≫ pullback.snd p f)) ≅
        FiniteEtale.fiber (xs ≫ (pullback.snd δ g ≫ pullback.snd p f)))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ α, fundamentalGroupHom (pullback.snd δ g ≫ pullback.snd p f) xs (sp α) =
        continuousConjAut t
          (fundamentalGroupHom (pullback.snd γ g ≫ pullback.snd p f) xη α) := by
  intro g γ δ
  obtain ⟨hC, hDVR, hH, hComplete, hSepC, Ω, hΩ, hΩclosed, i, η', hfield, hdata⟩ :=
    exists_dvrCompletionFamilyComparison D f p η o
  let C := AdicCompletion (maximalIdeal D) D
  let q := Spec.map (CommRingCat.ofHom (algebraMap D C))
  let ĝ := pullback.fst q g
  let γ' := Spec.map (CommRingCat.ofHom (η'.comp (algebraMap C (FractionRing C))))
  let o' := o.comp (dvrCompletionResidueEquiv D).symm.toRingHom
  let δ' := Spec.map (CommRingCat.ofHom (o'.comp (residue C)))
  obtain ⟨qη, qs, hηcart, hηtri, hscart, hstri, hηeq, hseq, hcleq, hcleq'⟩ := hdata
  have : (FiniteEtale.pullback qη).IsEquivalence := hηeq
  have : (FiniteEtale.pullback qs).IsEquivalence := hseq
  have : (FiniteEtale.pullback (pullback.snd δ' ĝ)).IsEquivalence := hcleq
  have : ConnectedSpace ↥(pullback γ' ĝ) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence qη).mpr hgeneric
  have : ConnectedSpace ↥(pullback δ' ĝ) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence qs).mpr hspecial
  have : ConnectedSpace ↥(pullback q g) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence (pullback.snd δ' ĝ)).mp
      inferInstance
  let yη : ↥(pullback γ' ĝ) := Classical.choice (inferInstance : Nonempty ↥(pullback γ' ĝ))
  let ys : ↥(pullback δ' ĝ) := Classical.choice (inferInstance : Nonempty ↥(pullback δ' ĝ))
  let Ωη := AlgebraicClosure ((pullback γ' ĝ).residueField yη)
  let Ωs := AlgebraicClosure ((pullback δ' ĝ).residueField ys)
  let xη : Spec (.of Ωη) ⟶ pullback γ' ĝ :=
    Spec.map (CommRingCat.ofHom
      (algebraMap ((pullback γ' ĝ).residueField yη) Ωη)) ≫
        (pullback γ' ĝ).fromSpecResidueField yη
  let xs : Spec (.of Ωs) ⟶ pullback δ' ĝ :=
    Spec.map (CommRingCat.ofHom
      (algebraMap ((pullback δ' ĝ).residueField ys) Ωs)) ≫
        (pullback δ' ĝ).fromSpecResidueField ys
  obtain ⟨t⟩ := nonempty_fiber_iso (xη ≫ pullback.snd γ' ĝ) (xs ≫ pullback.snd δ' ĝ)
  let ej : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xs ≫ pullback.snd δ' ĝ) :=
    autEquivOfCompIsoOfEquivalence (FiniteEtale.pullback (pullback.snd δ' ĝ))
      (pullbackFiberIso (pullback.snd δ' ĝ) xs)
  let spHat : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs) :=
    (ContinuousMonoidHom.toContinuousMonoidHom ej.symm).comp
      ((ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut t)).comp
        (fundamentalGroupHom (pullback.snd γ' ĝ) xη))
  have hhat (b : π₁ᵉᵗ(xη)) :
      fundamentalGroupHom (pullback.snd δ' ĝ) xs (spHat b) =
        continuousConjAut t (fundamentalGroupHom (pullback.snd γ' ĝ) xη b) := by
    exact (fundamentalGroupEquivalence_apply (pullback.snd δ' ĝ) xs
      (spHat b)).symm.trans
        (ej.apply_symm_apply (continuousConjAut t
          (fundamentalGroupHom (pullback.snd γ' ĝ) xη b)))
  obtain ⟨tOld, sp, hsp⟩ := transportSpecializationThroughFiberComparisons
    qη qs (pullback.snd γ' ĝ) (pullback.snd δ' ĝ)
    (pullback.snd γ g ≫ pullback.snd p f) (pullback.snd δ g ≫ pullback.snd p f)
    (pullback.snd q g ≫ pullback.snd p f) hηtri hstri xη xs t spHat hhat
  exact ⟨Ωη, inferInstance, inferInstance, Ωs, inferInstance, inferInstance,
    xη ≫ qη, xs ≫ qs, tOld, sp, hsp⟩

/-- Complete the actual DVR family, choose geometric points on its two
fibres, and obtain specialization on the original DVR geometric fibres.
The path and triangle are on the original total space `X`. -/
theorem exists_dvrCompletionSpecialization
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsSepClosed (ResidueField D)]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (p : Spec (.of D) ⟶ S)
    {K k : Type u} [Field K] [IsSepClosed K] [Field k] [IsSepClosed k]
    (η : FractionRing D →+* K) (o : ResidueField D →+* k) :
    let g := pullback.fst p f
    let γ := Spec.map (CommRingCat.ofHom η) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))
    let δ := Spec.map (CommRingCat.ofHom (o.comp (residue D)))
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback γ g) (xs : Spec (.of Ωs) ⟶ pullback δ g)
      (t : FiniteEtale.fiber (xη ≫ (pullback.snd γ g ≫ pullback.snd p f)) ≅
        FiniteEtale.fiber (xs ≫ (pullback.snd δ g ≫ pullback.snd p f)))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ α, fundamentalGroupHom (pullback.snd δ g ≫ pullback.snd p f) xs (sp α) =
        continuousConjAut t
          (fundamentalGroupHom (pullback.snd γ g ≫ pullback.snd p f) xη α) := by
  have hgeneric : ConnectedSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom η) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D))))
      (pullback.fst p f)) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst _ _)
  have hspecial : ConnectedSpace ↥(pullback
      (Spec.map (CommRingCat.ofHom (o.comp (residue D)))) (pullback.fst p f)) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst _ _)
  exact exists_dvrCompletionSpecialization_of_connectedFibers D f p η o hgeneric hspecial

end EtaleFundamentalGroups.StrictHenselian

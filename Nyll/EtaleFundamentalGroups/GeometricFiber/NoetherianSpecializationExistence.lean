/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.DVRCompletionSpecialization
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ConnectedComponents
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationDVR
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison
public import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
public import Nyll.EtaleFundamentalGroups.StrictHenselian.SpecializationSpecifiedLift
public import Nyll.SchemeTheory.LocalGeometry.SpecializationStalkMap
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Specialization existence over a locally Noetherian base

A specified strict-local lift gives an actual DVR family. Completing it
constructs specialization on its geometric fibers; the actual field
comparisons transport that map to the original geometric fibers. The
result retains a path and the triangle to the original total space.
For an algebraically closed generic pointing field, the strict-local lift
is supplied from the specialization itself.

This proves existence by the DVR-completion construction. Independence
of the chosen DVR/completion and the general naturality/composition
theorems are separate statements; they are not assumed or asserted here.
Reference: the construction underlying Stacks 58.16 (0BUP).
https://stacks.math.columbia.edu/tag/0BUP
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory IsLocalRing
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- A chosen lift and connectedness of the two specified geometric fibers
suffice for specialization over a locally Noetherian base. All DVR and
completion comparisons are constructed, and the triangle is on the
original total space. No condition is imposed on the other fibers. -/
theorem exists_noetherianFamilySpecialization_of_connectedFibers
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsSepClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* kt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint ks)) t h).hom)
    (hgeneric : ConnectedSpace ↥(pullback t f))
    (hspecial : ConnectedSpace ↥(pullback s f)) :
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f)
      (τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ a, FiniteEtale.fundamentalGroupHom (pullback.snd s f) xs (sp a) =
        continuousConjAut τ (FiniteEtale.fundamentalGroupHom (pullback.snd t f) xη a) := by
  obtain ⟨K, hK, hKc, k, hk, hkc, i, j, D, hD, hH, hDVR, hDr,
    α, η, o, hα, hη, hρ, hdata⟩ :=
      exists_dvrFamily_of_specializationLift f s t h ψ hψ
  let p := Spec.map (CommRingCat.ofHom α) ≫ localGeometricStalkToScheme s
  let g := pullback.fst p f
  let γ := Spec.map (CommRingCat.ofHom η) ≫
    Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))
  let δ := Spec.map (CommRingCat.ofHom (o.comp (residue D)))
  obtain ⟨qη, qs, qr, hηcart, hηtri, hscart, hstri, hrcart, hrtri, hηeq, hseq, hreq⟩ :=
    hdata
  have : (FiniteEtale.pullback qη).IsEquivalence := hηeq
  have : (FiniteEtale.pullback qs).IsEquivalence := hseq
  have hgenericD : ConnectedSpace ↥(pullback γ g) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence qη).mpr hgeneric
  have hspecialD : ConnectedSpace ↥(pullback δ g) :=
    (FiniteEtale.connectedSpace_iff_of_pullback_isEquivalence qs).mpr hspecial
  obtain ⟨Ωη, hΩη, hΩηc, Ωs, hΩs, hΩsc, xη, xs, τ, sp, hsp⟩ :=
    exists_dvrCompletionSpecialization_of_connectedFibers D f p η o hgenericD hspecialD
  let jη := pullback.snd γ g ≫ pullback.snd p f
  let js := pullback.snd δ g ≫ pullback.snd p f
  have hη' : qη ≫ pullback.snd t f = jη ≫ 𝟙 X :=
    hηtri.trans (Category.comp_id jη).symm
  have hs' : qs ≫ pullback.snd s f = js ≫ 𝟙 X :=
    hstri.trans (Category.comp_id js).symm
  obtain ⟨τ', sp', hsp'⟩ := transportSpecializationThroughFiberComparisons
    qη qs jη js (pullback.snd t f) (pullback.snd s f) (𝟙 X)
      hη' hs' xη xs τ sp hsp
  exact ⟨Ωη, hΩη, hΩηc, Ωs, hΩs, hΩsc, xη ≫ qη, xs ≫ qs, τ', sp', hsp'⟩

/-- A chosen lift over a locally Noetherian base yields a continuous map
on the original geometric fibers, with geometric basepoints, a path, and
the total-space triangle. All DVR and completion comparisons are constructed. -/
theorem exists_noetherianFamilySpecialization
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsSepClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    (ψ : geometricStalk
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)) →+* kt)
    (hψ : ψ.comp (geometricStalkStructureMap (Scheme.stalkClosedPointTo s).hom) =
      (Scheme.stalkSpecializationToField (s (closedPoint ks)) t h).hom) :
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f)
      (τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ a, FiniteEtale.fundamentalGroupHom (pullback.snd s f) xs (sp a) =
        continuousConjAut τ (FiniteEtale.fundamentalGroupHom (pullback.snd t f) xη a) := by
  have hgeneric : ConnectedSpace ↥(pullback t f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst t f)
  have hspecial : ConnectedSpace ↥(pullback s f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst s f)
  exact exists_noetherianFamilySpecialization_of_connectedFibers
    f s t h ψ hψ hgeneric hspecial

/-- A specialization with algebraically closed generic pointing field and
two connected geometric fibers supplies its own strict-local lift. The
result includes the actual path and triangle to the original total space. -/
theorem exists_noetherianFamilySpecialization_of_specializes_of_connectedFibers
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsAlgClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    (hgeneric : ConnectedSpace ↥(pullback t f))
    (hspecial : ConnectedSpace ↥(pullback s f)) :
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f)
      (τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ a, FiniteEtale.fundamentalGroupHom (pullback.snd s f) xs (sp a) =
        continuousConjAut τ (FiniteEtale.fundamentalGroupHom (pullback.snd t f) xη a) := by
  obtain ⟨ψ, hψ, hscheme⟩ := exists_localGeometricStalk_specifiedSpecializationLift s t h
  exact exists_noetherianFamilySpecialization_of_connectedFibers
    f s t h ψ hψ hgeneric hspecial

/-- Over a locally Noetherian base, a specialization of geometric points
with algebraically closed generic pointing field supplies a continuous
map on the original geometric fibers. No strict-local lift or completion
comparison is an input. The path and total-space triangle are constructed. -/
theorem exists_noetherianFamilySpecialization_of_specializes
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsAlgClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks)) :
    ∃ (Ωη : Type u) (_ : Field Ωη) (_ : IsAlgClosed Ωη)
      (Ωs : Type u) (_ : Field Ωs) (_ : IsAlgClosed Ωs)
      (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f)
      (τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f))
      (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs)),
      ∀ a, FiniteEtale.fundamentalGroupHom (pullback.snd s f) xs (sp a) =
        continuousConjAut τ (FiniteEtale.fundamentalGroupHom (pullback.snd t f) xη a) := by
  obtain ⟨ψ, hψ, hscheme⟩ := exists_localGeometricStalk_specifiedSpecializationLift s t h
  exact exists_noetherianFamilySpecialization f s t h ψ hψ

/-- Paths on the two connected fibres transport a specialization and its
total-space triangle to arbitrary supplied geometric basepoints. The
total-space path is constructed by the actual pullback-fibre comparisons. -/
theorem exists_specialization_at_geometric_basepoints
    {T U X : Scheme.{u}} [ConnectedSpace T] [ConnectedSpace U]
    (pη : T ⟶ X) (ps : U ⟶ X)
    {Ωη Ωs Ωη' Ωs' : Type u}
    [Field Ωη] [IsSepClosed Ωη] [Field Ωs] [IsSepClosed Ωs]
    [Field Ωη'] [IsSepClosed Ωη'] [Field Ωs'] [IsSepClosed Ωs']
    (xη : Spec (.of Ωη) ⟶ T) (xs : Spec (.of Ωs) ⟶ U)
    (yη : Spec (.of Ωη') ⟶ T) (ys : Spec (.of Ωs') ⟶ U)
    (τ : FiniteEtale.fiber (xη ≫ pη) ≅ FiniteEtale.fiber (xs ≫ ps))
    (sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs))
    (hsp : ∀ a, fundamentalGroupHom ps xs (sp a) =
      continuousConjAut τ (fundamentalGroupHom pη xη a)) :
    ∃ τ' : FiniteEtale.fiber (yη ≫ pη) ≅ FiniteEtale.fiber (ys ≫ ps),
      ∃ sp' : π₁ᵉᵗ(yη) →ₜ* π₁ᵉᵗ(ys), ∀ a,
        fundamentalGroupHom ps ys (sp' a) =
          continuousConjAut τ' (fundamentalGroupHom pη yη a) := by
  obtain ⟨aη⟩ := nonempty_fiber_iso yη xη
  obtain ⟨as⟩ := nonempty_fiber_iso xs ys
  let tη : FiniteEtale.fiber (yη ≫ pη) ≅ FiniteEtale.fiber (xη ≫ pη) :=
    (pullbackFiberIso pη yη).symm ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback pη) aη ≪≫ pullbackFiberIso pη xη
  let ts : FiniteEtale.fiber (xs ≫ ps) ≅ FiniteEtale.fiber (ys ≫ ps) :=
    (pullbackFiberIso ps xs).symm ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback ps) as ≪≫ pullbackFiberIso ps ys
  let τ' : FiniteEtale.fiber (yη ≫ pη) ≅ FiniteEtale.fiber (ys ≫ ps) :=
    tη ≪≫ τ ≪≫ ts
  let sp' : π₁ᵉᵗ(yη) →ₜ* π₁ᵉᵗ(ys) :=
    (ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut as)).comp
      (sp.comp (ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut aη)))
  have hη (a : π₁ᵉᵗ(yη)) :
      tη.conjAut (fundamentalGroupHom pη yη a) =
        fundamentalGroupHom pη xη (aη.conjAut a) :=
    fundamentalGroupHom_conjAut pη yη xη aη a
  have hs (a : π₁ᵉᵗ(xs)) :
      ts.conjAut (fundamentalGroupHom ps xs a) =
        fundamentalGroupHom ps ys (as.conjAut a) :=
    fundamentalGroupHom_conjAut ps xs ys as a
  refine ⟨τ', sp', ?_⟩
  intro a
  change fundamentalGroupHom ps ys (as.conjAut (sp (aη.conjAut a))) =
    (tη ≪≫ τ ≪≫ ts).conjAut (fundamentalGroupHom pη yη a)
  calc
    _ = ts.conjAut (fundamentalGroupHom ps xs (sp (aη.conjAut a))) := (hs _).symm
    _ = ts.conjAut (τ.conjAut (fundamentalGroupHom pη xη (aη.conjAut a))) :=
      congrArg ts.conjAut (hsp (aη.conjAut a))
    _ = ts.conjAut (τ.conjAut (tη.conjAut (fundamentalGroupHom pη yη a))) :=
      congrArg (fun b => ts.conjAut (τ.conjAut b)) (hη a).symm
    _ = _ := ((Iso.trans_conjAut tη (τ ≪≫ ts) _).trans
      (Iso.trans_conjAut τ ts _)).symm

/-- For a proper family over a locally Noetherian base, connectedness of
only the two specified geometric fibers gives specialization at arbitrary
supplied geometric basepoints, with its original total-space triangle. -/
theorem exists_noetherianFamilySpecialization_at_points_of_connectedFibers
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsAlgClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    (hgeneric : ConnectedSpace ↥(pullback t f))
    (hspecial : ConnectedSpace ↥(pullback s f))
    {Ωη Ωs : Type u} [Field Ωη] [IsSepClosed Ωη] [Field Ωs] [IsSepClosed Ωs]
    (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f) :
    ∃ τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f),
      ∃ sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs), ∀ a,
        fundamentalGroupHom (pullback.snd s f) xs (sp a) =
          continuousConjAut τ (fundamentalGroupHom (pullback.snd t f) xη a) := by
  obtain ⟨Ωη₀, hΩη₀, hΩη₀c, Ωs₀, hΩs₀, hΩs₀c, xη₀, xs₀, τ₀, sp₀, hsp₀⟩ :=
    exists_noetherianFamilySpecialization_of_specializes_of_connectedFibers
      f s t h hgeneric hspecial
  exact exists_specialization_at_geometric_basepoints
    (pullback.snd t f) (pullback.snd s f) xη₀ xs₀ xη xs τ₀ sp₀ hsp₀

/-- A proper geometrically connected family over a locally Noetherian
base has specialization at the supplied geometric basepoints. The lift
into the given algebraically closed generic pointing field is constructed. -/
theorem exists_noetherianFamilySpecialization_at_points
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    {ks kt : Type u} [Field ks] [IsSepClosed ks] [Field kt] [IsAlgClosed kt]
    (s : Spec (.of ks) ⟶ S) (t : Spec (.of kt) ⟶ S)
    (h : t (closedPoint kt) ⤳ s (closedPoint ks))
    {Ωη Ωs : Type u} [Field Ωη] [IsSepClosed Ωη] [Field Ωs] [IsSepClosed Ωs]
    (xη : Spec (.of Ωη) ⟶ pullback t f) (xs : Spec (.of Ωs) ⟶ pullback s f) :
    ∃ τ : FiniteEtale.fiber (xη ≫ pullback.snd t f) ≅
        FiniteEtale.fiber (xs ≫ pullback.snd s f),
      ∃ sp : π₁ᵉᵗ(xη) →ₜ* π₁ᵉᵗ(xs), ∀ a,
        fundamentalGroupHom (pullback.snd s f) xs (sp a) =
          continuousConjAut τ (fundamentalGroupHom (pullback.snd t f) xη a) := by
  have hgeneric : ConnectedSpace ↥(pullback t f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst t f)
  have hspecial : ConnectedSpace ↥(pullback s f) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst s f)
  exact exists_noetherianFamilySpecialization_at_points_of_connectedFibers
    f s t h hgeneric hspecial xη xs

end EtaleFundamentalGroups.StrictHenselian

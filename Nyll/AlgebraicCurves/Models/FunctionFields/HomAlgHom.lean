/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_hom_of_algHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.PartialMapMemDomainToRationalMap
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ValuationRingStalkSmoothOfRelativeDimensionOne
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Flat.TorsionFree
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Curve Model exists hom of alg Hom
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_exists_hom_of_algHom

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

namespace HG1A

section Spread

variable {X Y S : Scheme.{u}}

private theorem mem_domain_of_valuationRing (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X]
    [LocallyOfFiniteType sY] (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y)
    (hf : f.hom ≫ sY = f.domain.ι ≫ sX) (x : X) (hx : ValuationRing (X.presheaf.stalk x)) :
    x ∈ f.toRationalMap.domain :=
  _root_.AlgebraicGeometry.Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
    sX sY hY f hf x hx

end Spread

section LocalRings

private theorem valuationRing_stalk {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [SmoothOfRelativeDimension 1 c] (x : C) :
    ValuationRing (C.presheaf.stalk x) :=
  _root_.AlgebraicGeometry.valuationRing_stalk_of_smoothOfRelativeDimension_one c x

end LocalRings

section Generic

variable {K : Type u} [Field K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']

private abbrev ffHom (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F') :
    M.C.functionField →+* M'.C.functionField :=
  M'.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)

private abbrev genericHom (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F') :
    Spec M'.C.functionField ⟶ M.C :=
  Spec.map (CommRingCat.ofHom (ffHom M M' φ)) ≫ M.C.fromSpecStalk (genericPoint M.C)

private theorem fromSpecStalk_genericPoint_comp_eq {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) :
    C.fromSpecStalk (genericPoint C) ≫ c =
      Spec.map (CommRingCat.ofHom (baseToFunctionField c)) :=
  _root_.AlgebraicCurve.fromSpecStalk_genericPoint_comp_base c

private theorem ffHom_comp_baseToFunctionField (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') :
    (ffHom M M' φ).comp (baseToFunctionField M.toBase) = baseToFunctionField M'.toBase := by
  ext a
  change M'.ffEquiv (φ (M.ffEquiv.symm (baseToFunctionField M.toBase a))) =
    baseToFunctionField M'.toBase a
  rw [← M.ffEquiv_algebraMap a, RingEquiv.symm_apply_apply, φ.commutes, M'.ffEquiv_algebraMap]

private theorem genericHom_comp_toBase (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') :
    genericHom M M' φ ≫ M.toBase = M'.C.fromSpecStalk (genericPoint M'.C) ≫ M'.toBase := by
  let f : M.C.functionField ⟶ M'.C.functionField := CommRingCat.ofHom (ffHom M M' φ)
  let a : CommRingCat.of K ⟶ M.C.functionField :=
    CommRingCat.ofHom (baseToFunctionField M.toBase)
  let a' : CommRingCat.of K ⟶ M'.C.functionField :=
    CommRingCat.ofHom (baseToFunctionField M'.toBase)
  have hcomp : a ≫ f = a' := by
    ext k
    exact RingHom.congr_fun (ffHom_comp_baseToFunctionField M M' φ) k
  calc
    genericHom M M' φ ≫ M.toBase =
        Spec.map f ≫ (M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase) :=
      Category.assoc _ _ _
    _ = Spec.map f ≫ Spec.map a := congrArg (fun g => Spec.map f ≫ g)
      (fromSpecStalk_genericPoint_comp_eq M.toBase)
    _ = Spec.map (a ≫ f) := (Spec.map_comp a f).symm
    _ = Spec.map a' := congrArg (fun g : CommRingCat.of K ⟶ M'.C.functionField => Spec.map g) hcomp
    _ = M'.C.fromSpecStalk (genericPoint M'.C) ≫ M'.toBase :=
      (fromSpecStalk_genericPoint_comp_eq M'.toBase).symm

private theorem isSeparated_of_over {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of K))
    [IsSeparated g] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

private theorem existence_of_isProper {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] :
    ValuativeCriterion.Existence g := by
  have h : IsProper g := inferInstance
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1.existence

private theorem exists_hom_comp_toBase_eq (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') :
    ∃ π : M'.C ⟶ M.C, π ≫ M.toBase = M'.toBase ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ := by
  have : M.C.IsSeparated := isSeparated_of_over M.toBase
  have hψ := genericHom_comp_toBase M M' φ
  let f₀ : M'.C.PartialMap M.C :=
    Scheme.PartialMap.ofFromSpecStalk M'.toBase M.toBase (genericHom M M' φ) hψ
  have hf₀ : f₀.hom ≫ M.toBase = f₀.domain.ι ≫ M'.toBase :=
    Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _
  have hη : genericPoint M'.C ∈ f₀.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hf₀η : f₀.fromSpecStalkOfMem hη = genericHom M M' φ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  have hdom : f₀.toRationalMap.domain = ⊤ := top_unique fun x _ =>
    mem_domain_of_valuationRing M'.toBase M.toBase (existence_of_isProper M.toBase) f₀ hf₀ x
      (valuationRing_stalk M'.toBase x)
  let g := f₀.toRationalMap.toPartialMap
  let π : M'.C ⟶ M.C := M'.C.topIso.inv ≫ M'.C.homOfLE hdom.ge ≫ g.hom
  have hι : f₀.domain.ι ≫ π = f₀.hom := by
    have key := f₀.toPartialMap_toRationalMap_restrict
    change M'.C.homOfLE f₀.le_domain_toRationalMap ≫ g.hom = f₀.hom at key
    rw [← key]
    change f₀.domain.ι ≫ M'.C.topIso.inv ≫ M'.C.homOfLE hdom.ge ≫ g.hom =
      M'.C.homOfLE f₀.le_domain_toRationalMap ≫ g.hom
    have hι' : f₀.domain.ι ≫ M'.C.topIso.inv ≫ M'.C.homOfLE hdom.ge =
        M'.C.homOfLE f₀.le_domain_toRationalMap := by
      apply (cancel_mono g.domain.ι).mp
      change (f₀.domain.ι ≫ M'.C.topIso.inv ≫ M'.C.homOfLE hdom.ge) ≫
        f₀.toRationalMap.domain.ι = M'.C.homOfLE f₀.le_domain_toRationalMap ≫
          f₀.toRationalMap.domain.ι
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.toIso_inv_ι, Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun j => j ≫ g.hom) hι')
  refine ⟨π, ?_, ?_⟩
  · have : IsDominant f₀.domain.ι :=
      ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact f₀.dense_domain⟩
    refine ext_of_isDominant f₀.domain.ι ?_
    rw [reassoc_of% hι, hf₀]
  · rw [← Scheme.Opens.fromSpecStalkOfMem_ι f₀.domain (genericPoint M'.C) hη, Category.assoc, hι]
    exact hf₀η

private theorem isDominant_fromSpecStalk_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  refine ⟨?_⟩
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk (genericPoint X)) :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have hd : Dense ({genericPoint X} : Set X) :=
    dense_iff_closure_eq.mpr (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.mpr hη)

private theorem apply_genericPoint_eq (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    π.base (genericPoint M'.C) = genericPoint M.C := by
  let z : Spec M'.C.functionField := IsLocalRing.closedPoint M'.C.functionField
  let w : Spec M.C.functionField := IsLocalRing.closedPoint M.C.functionField
  have hz : M'.C.fromSpecStalk (genericPoint M'.C) z = genericPoint M'.C :=
    Scheme.fromSpecStalk_closedPoint
  have hw : M.C.fromSpecStalk (genericPoint M.C) w = genericPoint M.C :=
    Scheme.fromSpecStalk_closedPoint
  have : Subsingleton ↥(Spec M.C.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum M.C.functionField))
  have he : Spec.map (CommRingCat.ofHom (ffHom M M' φ)) z = w :=
    Subsingleton.elim (α := Spec M.C.functionField) _ _
  calc
    π.base (genericPoint M'.C) = π (M'.C.fromSpecStalk (genericPoint M'.C) z) :=
      congrArg π hz.symm
    _ = (M'.C.fromSpecStalk (genericPoint M'.C) ≫ π) z :=
      (Scheme.Hom.comp_apply _ _ z).symm
    _ = genericHom M M' φ z := congrArg (fun g : Spec M'.C.functionField ⟶ M.C => g z) hd
    _ = M.C.fromSpecStalk (genericPoint M.C)
        (Spec.map (CommRingCat.ofHom (ffHom M M' φ)) z) := Scheme.Hom.comp_apply _ _ z
    _ = M.C.fromSpecStalk (genericPoint M.C) w := congrArg _ he
    _ = genericPoint M.C := hw

private theorem stalkMap_comp_stalkSpecializes (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M'.C) :
    π.stalkMap x ≫ M'.C.presheaf.stalkSpecializes (genericPoint_specializes x) =
      M.C.presheaf.stalkSpecializes (genericPoint_specializes (π.base x)) ≫
        CommRingCat.ofHom (ffHom M M' φ) := by
  let f : M.C.functionField ⟶ M'.C.functionField := CommRingCat.ofHom (ffHom M M' φ)
  change π.stalkMap x ≫ M'.C.presheaf.stalkSpecializes (genericPoint_specializes x) =
    M.C.presheaf.stalkSpecializes (genericPoint_specializes (π.base x)) ≫ f
  apply Spec.map_injective
  rw [← cancel_mono (M.C.fromSpecStalk (π.base x))]
  simp only [Spec.map_comp, Category.assoc]
  rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, hd]
  rfl

private theorem algebraMap_stalkMap_apply (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M'.C)
    (a : M.C.presheaf.stalk (π.base x)) :
    algebraMap (M'.C.presheaf.stalk x) M'.C.functionField ((π.stalkMap x).hom a) =
      ffHom M M' φ (algebraMap (M.C.presheaf.stalk (π.base x)) M.C.functionField a) := by
  have h := congrArg (fun g => g.hom a) (stalkMap_comp_stalkSpecializes M M' φ π hd x)
  exact h

private theorem valuationRing_stalk' (M : CurveModel K F) (x : M.C) :
    ValuationRing (M.C.presheaf.stalk x) :=
  valuationRing_stalk M.toBase x

private theorem eq_of_fromSpecStalk_comp_eq (M : CurveModel K F) (M' : CurveModel K F')
    {π π' : M'.C ⟶ M.C}
    (h : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π) :
    π' = π := by
  have : M.C.IsSeparated := isSeparated_of_over M.toBase
  have := isDominant_fromSpecStalk_genericPoint M'.C
  exact ext_of_isDominant (M'.C.fromSpecStalk (genericPoint M'.C)) h

end Generic

section Places

variable {K : Type u} [Field K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']

private def stalkRange (M : CurveModel K F) (x : M.C) : Subring F :=
  ((M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
    (algebraMap (M.C.presheaf.stalk x) M.C.functionField)).range

private theorem stalkRange_closedPoint (M : CurveModel K F) (x : closedPoints M.C) :
    stalkRange M x.1 = (M.placeOfPoint x).toValuationSubring.toSubring :=
  M.range_stalk_eq x

private theorem mem_stalkRange_closedPoint (M : CurveModel K F) (x : closedPoints M.C) (f : F) :
    f ∈ stalkRange M x.1 ↔ f ∈ (M.placeOfPoint x).toValuationSubring := by
  rw [stalkRange_closedPoint]
  exact ValuationSubring.mem_toSubring _ _

private theorem stalkRange_genericPoint (M : CurveModel K F) :
    stalkRange M (genericPoint M.C) = ⊤ := by
  rw [eq_top_iff]
  rintro g -
  simp only [stalkRange, RingHom.mem_range, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  refine ⟨M.ffEquiv g, ?_⟩
  rw [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
  exact M.ffEquiv.symm_apply_apply g

private theorem map_stalkRange_le (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (y : M'.C) :
    (stalkRange M (π.base y)).map φ.toRingHom ≤ stalkRange M' y := by
  intro g hg
  rw [Subring.mem_map] at hg
  obtain ⟨g, hg, rfl⟩ := hg
  simp only [stalkRange, RingHom.mem_range] at hg ⊢
  obtain ⟨a, rfl⟩ := hg
  refine ⟨(π.stalkMap y).hom a, ?_⟩
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [algebraMap_stalkMap_apply M M' φ π hd y a]
  simp [ffHom]

private theorem apply_mem_stalkRange (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (y : M'.C) {f : F}
    (hf : f ∈ stalkRange M (π.base y)) : φ f ∈ stalkRange M' y :=
  map_stalkRange_le M M' φ π hd y (Subring.mem_map.2 ⟨f, hf, rfl⟩)

private theorem eq_of_specializes (M : CurveModel K F) (x₀ : closedPoints M.C) {a b : M.C}
    (ha : a ⤳ x₀.1) (hb : b ⤳ x₀.1) (ha' : a ≠ x₀.1) (hb' : b ≠ x₀.1) : a = b := by
  let j : M.C.presheaf.stalk x₀.1 →+* F :=
    (M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
      (algebraMap (M.C.presheaf.stalk x₀.1) M.C.functionField)
  have hj : Function.Injective j :=
    M.ffEquiv.symm.injective.comp
      (IsFractionRing.injective (M.C.presheaf.stalk x₀.1) M.C.functionField)
  have : IsPrincipalIdealRing j.range := by
    change IsPrincipalIdealRing (stalkRange M x₀.1)
    rw [stalkRange_closedPoint]
    exact inferInstanceAs (IsPrincipalIdealRing (M.placeOfPoint x₀).toValuationSubring)
  have : IsPrincipalIdealRing (M.C.presheaf.stalk x₀.1) := by
    let e : M.C.presheaf.stalk x₀.1 ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
      ⟨fun p q h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
    exact IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  have key : ∀ p : PrimeSpectrum (M.C.presheaf.stalk x₀.1),
      M.C.fromSpecStalk x₀.1 p ≠ x₀.1 → p.asIdeal = ⊥ := by
    intro p hp
    by_contra hne
    apply hp
    have hmax : p.asIdeal = IsLocalRing.maximalIdeal (M.C.presheaf.stalk x₀.1) :=
      IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne p.isPrime)
    have hp' : p = IsLocalRing.closedPoint (M.C.presheaf.stalk x₀.1) := PrimeSpectrum.ext hmax
    rw [hp']
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨pa, hpa⟩ : a ∈ Set.range (M.C.fromSpecStalk x₀.1) := by
    rw [Scheme.range_fromSpecStalk]
    exact ha
  obtain ⟨pb, hpb⟩ : b ∈ Set.range (M.C.fromSpecStalk x₀.1) := by
    rw [Scheme.range_fromSpecStalk]
    exact hb
  have hab : pa = pb :=
    PrimeSpectrum.ext ((key pa (by rw [hpa]; exact ha')).trans
      (key pb (by rw [hpb]; exact hb')).symm)
  rw [← hpa, ← hpb, hab]

private theorem mem_closedPoints_or_eq_genericPoint (M : CurveModel K F) (x : M.C) :
    x ∈ closedPoints M.C ∨ x = genericPoint M.C := by
  by_cases hx : x ∈ closedPoints M.C
  · exact Or.inl hx
  right
  have : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨x₀, hxx₀, hx₀⟩ := nonempty_inter_closedPoints (X := M.C) (Z := closure {x})
    ⟨x, subset_closure (Set.mem_singleton x)⟩ isClosed_closure.isLocallyClosed
  have hspec : x ⤳ x₀ := specializes_iff_mem_closure.2 hxx₀
  have hne : x ≠ x₀ := fun h => hx (h ▸ hx₀)
  by_cases hη : genericPoint M.C = x₀
  · have hx' : x ⤳ genericPoint M.C := by
      rw [hη]
      exact hspec
    exact (hx'.antisymm (genericPoint_specializes x)).eq
  · exact eq_of_specializes M ⟨x₀, hx₀⟩ hspec (genericPoint_specializes x₀) hne hη

private theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F')
    (f : F) : f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

private theorem apply_ne_genericPoint (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (y : closedPoints M'.C) : π.base y.1 ≠ genericPoint M.C := by
  intro hgen
  apply ((M'.placeOfPoint y).restrictAlong φ hφ).ne_top'
  refine SetLike.ext fun f => ⟨fun _ => ValuationSubring.mem_top f, fun _ => ?_⟩
  rw [mem_restrictAlong_iff, ← mem_stalkRange_closedPoint]
  apply apply_mem_stalkRange M M' φ π hd y.1
  rw [hgen, stalkRange_genericPoint]
  exact Subring.mem_top f

private theorem apply_mem_closedPoints (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (y : closedPoints M'.C) : π.base y.1 ∈ closedPoints M.C :=
  (mem_closedPoints_or_eq_genericPoint M _).resolve_right (apply_ne_genericPoint M M' φ hφ π hd y)

private theorem ofPrime_eq_top_or_eq {A : ValuationSubring F} [IsDiscreteValuationRing A]
    (P : Ideal A)
    [P.IsPrime] : A.ofPrime P = ⊤ ∨ A.ofPrime P = A := by
  by_cases hP : P = ⊥
  · left
    subst hP
    exact ValuationSubring.ofPrime_bot A
  · right
    have hmax : P = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hP inferInstance)
    subst hmax
    exact ValuationSubring.ofPrime_top A

private theorem place_eq_of_le {v v' : Place K F}
    (h : v.toValuationSubring ≤ v'.toValuationSubring) : v = v' := by
  apply Place.ext
  have key := ValuationSubring.ofPrime_idealOfLE v.toValuationSubring v'.toValuationSubring h
  rcases ofPrime_eq_top_or_eq (v.toValuationSubring.idealOfLE v'.toValuationSubring h) with
    htop | heq
  · exact absurd (key.symm.trans htop) v'.ne_top'
  · exact (key.symm.trans heq).symm

private theorem exists_mem_closedPoints_placeOfPoint_eq (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (y : closedPoints M'.C) :
    ∃ h : π.base y.1 ∈ closedPoints M.C,
      M.placeOfPoint ⟨π.base y.1, h⟩ = (M'.placeOfPoint y).restrictAlong φ hφ := by
  have _ := hfin
  have _ := ha
  have h := apply_mem_closedPoints M M' φ hφ π hd y
  refine ⟨h, place_eq_of_le ?_⟩
  intro f hf
  rw [mem_restrictAlong_iff, ← mem_stalkRange_closedPoint M' y]
  apply apply_mem_stalkRange M M' φ π hd y.1
  exact (mem_stalkRange_closedPoint M ⟨π.base y.1, h⟩ f).2 hf

variable [CharZero K]

private theorem restrictAlong_fiber_finite (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (v : Place K F) :
    {w : Place K F' | w.restrictAlong φ hφ = v}.Finite := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have : Module.Finite F F' := hfin
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  exact Place.finite_setOf_restrict_eq (F := F) (F' := F') v

private theorem finite_preimage_singleton (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (x : M.C) : (π.base ⁻¹' {x}).Finite := by
  classical
  rcases mem_closedPoints_or_eq_genericPoint M x with hx | rfl
  · let T : Set (closedPoints M'.C) := {y | π.base y.1 = x}
    have hT : T.Finite := by
      refine Set.Finite.of_finite_image (f := fun y => M'.placeOfPoint y) ?_ ?_
      · refine (restrictAlong_fiber_finite φ hφ hfin (M.placeOfPoint ⟨x, hx⟩)).subset ?_
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨h, he⟩ := exists_mem_closedPoints_placeOfPoint_eq M M' φ hφ hfin π ha hd y
        change (M'.placeOfPoint y).restrictAlong φ hφ = M.placeOfPoint ⟨x, hx⟩
        rw [← he]
        congr 1
        exact Subtype.ext hy
      · exact fun y _ y' _ hyy' => M'.placeOfPoint_bijective.1 hyy'
    refine ((hT.image Subtype.val).union (Set.finite_singleton (genericPoint M'.C))).subset ?_
    intro y hy
    rcases mem_closedPoints_or_eq_genericPoint M' y with hy' | rfl
    · exact Or.inl ⟨⟨y, hy'⟩, hy, rfl⟩
    · exact Or.inr rfl
  · refine (Set.finite_singleton (genericPoint M'.C)).subset ?_
    intro y hy
    rcases mem_closedPoints_or_eq_genericPoint M' y with hy' | rfl
    · exact absurd hy (apply_ne_genericPoint M M' φ hφ π hd ⟨y, hy'⟩)
    · rfl

end Places

section Rank

variable {K : Type u} [Field K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']

private theorem isProper (M : CurveModel K F) (M' : CurveModel K F')
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase) : IsProper π := by
  have h : IsProper (π ≫ M.toBase) := by rw [ha]; infer_instance
  exact IsProper.of_comp π M.toBase

private theorem locallyOfFiniteType (M : CurveModel K F) (M' : CurveModel K F')
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase) : LocallyOfFiniteType π := by
  have h : LocallyOfFiniteType (π ≫ M.toBase) := by rw [ha]; infer_instance
  exact locallyOfFiniteType_of_comp π M.toBase

private theorem locallyQuasiFinite [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    LocallyQuasiFinite π := by
  have := isProper M M' π ha
  have := locallyOfFiniteType M M' π ha
  exact (locallyQuasiFinite_iff_finite_preimage_singleton (f := π)).mpr
    (fun x => finite_preimage_singleton M M' φ hφ hfin π ha hd x)

private theorem isFinite [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    IsFinite π := by
  have := isProper M M' π ha
  have := locallyQuasiFinite M M' φ hφ hfin π ha hd
  exact IsFinite.of_isProper_of_locallyQuasiFinite π

private theorem stalkMap_injective (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M'.C) :
    Function.Injective (π.stalkMap x).hom := by
  intro a b hab
  have h := congrArg (algebraMap (M'.C.presheaf.stalk x) M'.C.functionField) hab
  rw [algebraMap_stalkMap_apply M M' φ π hd x a, algebraMap_stalkMap_apply M M' φ π hd x b] at h
  exact IsFractionRing.injective (M.C.presheaf.stalk (π.base x)) M.C.functionField
    ((ffHom M M' φ).injective h)

private theorem flat_of_injective_of_valuationRing {A B : Type u} [CommRing A] [IsDomain A]
    [ValuationRing A] [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Injective f) :
    f.Flat := by
  let : Algebra A B := f.toAlgebra
  change Module.Flat A B
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  intro b hb
  obtain ⟨⟨a, ha⟩, hab⟩ := (Submodule.mem_torsion_iff b).mp hb
  have hab' : f a * b = 0 := hab
  rcases mul_eq_zero.mp hab' with h | h
  · exact absurd ((map_eq_zero_iff f hf).mp h) (nonZeroDivisors.ne_zero ha)
  · exact h

private theorem flat_stalkMap (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M'.C) :
    (π.stalkMap x).hom.Flat := by
  have := valuationRing_stalk' M (π.base x)
  exact flat_of_injective_of_valuationRing (π.stalkMap x).hom
    (stalkMap_injective M M' φ π hd x)

private theorem flat (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    Flat π := by
  have _ := hφ
  have _ := hfin
  have _ := ha
  exact Flat.of_stalkMap π (fun x => flat_stalkMap M M' φ π hd x)

private theorem locallyOfFinitePresentation_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] : LocallyOfFinitePresentation f :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

private theorem isLocallyNoetherian (M : CurveModel K F) : IsLocallyNoetherian M.C :=
  LocallyOfFiniteType.isLocallyNoetherian M.toBase

private theorem locallyOfFinitePresentation (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    LocallyOfFinitePresentation π := by
  have _ := hφ
  have _ := hfin
  have _ := hd
  have := isLocallyNoetherian M
  have := locallyOfFiniteType M M' π ha
  exact locallyOfFinitePresentation_of_locallyOfFiniteType π

private theorem finrank_eq_finrank_genericPoint [CharZero K] (M : CurveModel K F)
    (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) (x : M.C) :
    π.finrank x = π.finrank (genericPoint M.C) := by
  have := isFinite M M' φ hφ hfin π ha hd
  have := flat M M' φ hφ hfin π ha hd
  have := locallyOfFinitePresentation M M' φ hφ hfin π ha hd
  have hc : IsLocallyConstant π.finrank := Scheme.Hom.isLocallyConstant_finrank π
  exact hc.apply_eq_of_preconnectedSpace x (genericPoint M.C)

private theorem rankAtStalk_bot_eq_finrank {A B KA KB : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]
    [Field KA] [Algebra A KA] [IsFractionRing A KA] [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Algebra KA KB] [Algebra A KB] [IsScalarTower A B KB] [IsScalarTower A KA KB] :
    Module.rankAtStalk (R := A) B ⊥ = Module.finrank KA KB := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  rw [IsFractionRing.finrank_eq A KA B KB]
  have hp : (⊥ : Ideal A).primeCompl ≤ nonZeroDivisors A := (Ideal.primeCompl_bot (α := A)).le
  change Module.finrank (Localization.AtPrime (⊥ : Ideal A))
      (LocalizedModule (⊥ : Ideal A).primeCompl B) = Module.finrank A B
  rw [Module.finrank, IsLocalization.rank_eq (Localization.AtPrime (⊥ : Ideal A))
    (⊥ : Ideal A).primeCompl hp]
  exact IsLocalizedModule.finrank_eq (⊥ : Ideal A).primeCompl
    (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl B) hp

private theorem genericPoint_mem_preimage (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    {U : M.C.Opens} (hη : genericPoint M.C ∈ U) : genericPoint M'.C ∈ π ⁻¹ᵁ U := by
  change π.base (genericPoint M'.C) ∈ U
  rw [apply_genericPoint_eq M M' φ π hd]
  exact hη

private theorem algebraMap_germ (M : CurveModel K F) (U : M.C.Opens) (hη : genericPoint M.C ∈ U)
    (x : M.C) (hx : x ∈ U) (b : Γ(M.C, U)) :
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    @algebraMap (M.C.presheaf.stalk x) M.C.functionField _ _ (stalkFunctionFieldAlgebra M.C x)
        ((M.C.presheaf.germ U x hx).hom b) =
      algebraMap Γ(M.C, U) M.C.functionField b := by
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  change (M.C.presheaf.stalkSpecializes _).hom ((M.C.presheaf.germ U x hx).hom b) =
    (M.C.presheaf.germ U (genericPoint M.C) _).hom b
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]

private theorem algebraMap_app_apply (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hη : genericPoint M.C ∈ U) (a : Γ(M.C, U)) :
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, genericPoint_mem_preimage M M' φ π hd hη⟩⟩
    algebraMap Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField ((π.app U).hom a) =
      ffHom M M' φ (algebraMap Γ(M.C, U) M.C.functionField a) := by
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  have hη' : genericPoint M'.C ∈ π ⁻¹ᵁ U := genericPoint_mem_preimage M M' φ π hd hη
  have hx : π.base (genericPoint M'.C) ∈ U := hη'
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hη'⟩⟩
  calc algebraMap Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField ((π.app U).hom a)
      = @algebraMap (M'.C.presheaf.stalk (genericPoint M'.C)) M'.C.functionField _ _
          (stalkFunctionFieldAlgebra M'.C (genericPoint M'.C))
          ((M'.C.presheaf.germ (π ⁻¹ᵁ U) (genericPoint M'.C) hη').hom ((π.app U).hom a)) :=
        (algebraMap_germ M' (π ⁻¹ᵁ U) hη' (genericPoint M'.C) hη' ((π.app U).hom a)).symm
    _ = @algebraMap (M'.C.presheaf.stalk (genericPoint M'.C)) M'.C.functionField _ _
          (stalkFunctionFieldAlgebra M'.C (genericPoint M'.C))
          ((π.stalkMap (genericPoint M'.C)).hom
            ((M.C.presheaf.germ U (π.base (genericPoint M'.C)) hx).hom a)) :=
        congrArg (@algebraMap (M'.C.presheaf.stalk (genericPoint M'.C)) M'.C.functionField
            _ _ (stalkFunctionFieldAlgebra M'.C (genericPoint M'.C)))
          (Scheme.Hom.germ_stalkMap_apply π U (genericPoint M'.C) hx a).symm
    _ = ffHom M M' φ (@algebraMap (M.C.presheaf.stalk (π.base (genericPoint M'.C)))
          M.C.functionField _ _ (stalkFunctionFieldAlgebra M.C (π.base (genericPoint M'.C)))
          ((M.C.presheaf.germ U (π.base (genericPoint M'.C)) hx).hom a)) :=
        algebraMap_stalkMap_apply M M' φ π hd (genericPoint M'.C) _
    _ = ffHom M M' φ (algebraMap Γ(M.C, U) M.C.functionField a) :=
        congrArg (ffHom M M' φ) (algebraMap_germ M U hη (π.base (genericPoint M'.C)) hx a)

private theorem injective_app (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F')
    (π : M'.C ⟶ M.C)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hη : genericPoint M.C ∈ U) : Function.Injective (π.app U).hom := by
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, genericPoint_mem_preimage M M' φ π hd hη⟩⟩
  intro a b hab
  have h := congrArg (algebraMap Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField) hab
  rw [algebraMap_app_apply M M' φ π hd U hη a, algebraMap_app_apply M M' φ π hd U hη b] at h
  exact M.C.germToFunctionField_injective U ((ffHom M M' φ).injective h)

private theorem isPullback_fromSpec (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (π ⁻¹ᵁ U)) :
    IsPullback hV.fromSpec (Spec.map (π.app U)) π hU.fromSpec := by
  have _ := hφ
  have _ := hfin
  have _ := ha
  have _ := hd
  refine (IsOpenImmersion.isPullback (Spec.map (π.app U)) hV.fromSpec hU.fromSpec π ?_ ?_).flip
  · rw [Scheme.Hom.app_eq_appLE]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec π hU hV le_rfl).symm
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

private theorem finite_app [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hU : IsAffineOpen U) : (π.app U).hom.Finite := by
  have := isFinite M M' φ hφ hfin π ha hd
  exact (IsFinite.SpecMap_iff _).mp
    (MorphismProperty.of_isPullback (P := @IsFinite)
      (isPullback_fromSpec M M' φ hφ hfin π ha hd U hU (hU.preimage π))
      (inferInstanceAs (IsFinite π)))

private theorem flat_app [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hU : IsAffineOpen U) : (π.app U).hom.Flat := by
  have := isFinite M M' φ hφ hfin π ha hd
  have := flat M M' φ hφ hfin π ha hd
  exact Flat.SpecMap_iff.mp
    (MorphismProperty.of_isPullback (P := @Flat)
      (isPullback_fromSpec M M' φ hφ hfin π ha hd U hU (hU.preimage π))
      (inferInstanceAs (Flat π)))

private theorem fromSpec_bot (M : CurveModel K F) (U : M.C.Opens) (hU : IsAffineOpen U)
    (hη : genericPoint M.C ∈ U) :
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    hU.fromSpec (⊥ : PrimeSpectrum Γ(M.C, U)) = genericPoint M.C := by
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  have h := hU.fromSpec_primeIdealOf ⟨genericPoint M.C, hη⟩
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine] at h
  exact h

private theorem finrank_genericPoint_eq_ringHom_finrank [CharZero K] (M : CurveModel K F)
    (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (U : M.C.Opens) (hU : IsAffineOpen U) (hη : genericPoint M.C ∈ U) :
    haveI : Nonempty U := ⟨⟨_, hη⟩⟩
    π.finrank (genericPoint M.C) = (π.app U).hom.finrank (⊥ : PrimeSpectrum Γ(M.C, U)) := by
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  have := isFinite M M' φ hφ hfin π ha hd
  have := flat M M' φ hφ hfin π ha hd
  have hb : hU.fromSpec (⊥ : PrimeSpectrum Γ(M.C, U)) = genericPoint M.C := fromSpec_bot M U hU hη
  have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_fromSpec M M' φ hφ hfin π ha hd U hU (hU.preimage π)) (⊥ : PrimeSpectrum Γ(M.C, U))
  rw [hb] at h1
  exact h1.symm.trans (congrFun (Scheme.Hom.finrank_SpecMap_eq_finrank
    (finite_app M M' φ hφ hfin π ha hd U hU) (flat_app M M' φ hφ hfin π ha hd U hU)) _)

private theorem finrank_functionField (M : CurveModel K F) (M' : CurveModel K F') (φ : F →ₐ[K] F') :
    let := (ffHom M M' φ).toAlgebra
    Module.finrank M.C.functionField M'.C.functionField = finrankAlong K φ := by
  intro sharedOwner1
  let := algebraAlong φ
  change Module.finrank M.C.functionField M'.C.functionField = Module.finrank F F'
  refine Algebra.finrank_eq_of_equiv_equiv M.ffEquiv.symm M'.ffEquiv.symm ?_
  ext x
  simp [ffHom, RingHom.algebraMap_toAlgebra]

private theorem finrank_genericPoint [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ) :
    π.finrank (genericPoint M.C) = finrankAlong K φ := by
  obtain ⟨U, hU, hmem⟩ := M.finset_subset_affineOpen {genericPoint M.C}
  have hη : genericPoint M.C ∈ U := hmem _ (Finset.mem_singleton_self _)
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  have hη' := genericPoint_mem_preimage M M' φ π hd hη
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hη'⟩⟩
  have hf := finrank_functionField M M' φ
  rw [finrank_genericPoint_eq_ringHom_finrank M M' φ hφ hfin π ha hd U hU hη, ← hf]
  let : Algebra Γ(M.C, U) Γ(M'.C, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  let : Algebra M.C.functionField M'.C.functionField := (ffHom M M' φ).toAlgebra
  let : Algebra Γ(M.C, U) M'.C.functionField :=
    ((algebraMap Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField).comp (π.app U).hom).toAlgebra
  have : Module.Finite Γ(M.C, U) Γ(M'.C, π ⁻¹ᵁ U) := finite_app M M' φ hφ hfin π ha hd U hU
  have : FaithfulSMul Γ(M.C, U) Γ(M'.C, π ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (injective_app M M' φ π hd U hη)
  have : IsFractionRing Γ(M.C, U) M.C.functionField :=
    functionField_isFractionRing_of_isAffineOpen M.C U hU
  have : IsFractionRing Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField :=
    functionField_isFractionRing_of_isAffineOpen M'.C (π ⁻¹ᵁ U)
      (by have := isFinite M M' φ hφ hfin π ha hd; exact hU.preimage π)
  have : IsScalarTower Γ(M.C, U) Γ(M'.C, π ⁻¹ᵁ U) M'.C.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  have : IsScalarTower Γ(M.C, U) M.C.functionField M'.C.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => algebraMap_app_apply M M' φ π hd U hη a
  exact rankAtStalk_bot_eq_finrank (A := Γ(M.C, U)) (B := Γ(M'.C, π ⁻¹ᵁ U))
    (KA := M.C.functionField) (KB := M'.C.functionField)

private theorem finrank_eq [CharZero K] (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (π : M'.C ⟶ M.C) (ha : π ≫ M.toBase = M'.toBase)
    (hd : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π = genericHom M M' φ)
    (x : M.C) : π.finrank x = finrankAlong K φ := by
  rw [finrank_eq_finrank_genericPoint M M' φ hφ hfin π ha hd x,
    finrank_genericPoint M M' φ hφ hfin π ha hd]

end Rank

end HG1A

open AlgebraicCurve.CurveModel HG1A in
theorem _root_.AlgebraicCurve.CurveModel.exists_hom_of_algHom {K : Type u} [Field K] [CharZero K]
    {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']
    (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) :
    ∃ π : M'.C ⟶ M.C,
      π ≫ M.toBase = M'.toBase ∧
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
      (∀ x : M.C, π.finrank x = finrankAlong K φ) ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π =
        Spec.map (CommRingCat.ofHom
          (M'.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      (∀ y : closedPoints M'.C, ∃ h : π.base y.1 ∈ closedPoints M.C,
        M.placeOfPoint ⟨π.base y.1, h⟩ = (M'.placeOfPoint y).restrictAlong φ hφ) ∧
      ∀ π' : M'.C ⟶ M.C,
        M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
          M'.C.fromSpecStalk (genericPoint M'.C) ≫ π → π' = π := by
  obtain ⟨π, ha, hd⟩ := exists_hom_comp_toBase_eq M M' φ
  exact ⟨π, ha, isFinite M M' φ hφ hfin π ha hd, flat M M' φ hφ hfin π ha hd,
    locallyOfFinitePresentation M M' φ hφ hfin π ha hd,
    fun x => finrank_eq M M' φ hφ hfin π ha hd x, hd,
    fun y => exists_mem_closedPoints_placeOfPoint_eq M M' φ hφ hfin π ha hd y,
    fun π' h => eq_of_fromSpecStalk_comp_eq M M' h⟩

end
end AlgebraicCurves.Models.Proofs.CurveModel_exists_hom_of_algHom
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

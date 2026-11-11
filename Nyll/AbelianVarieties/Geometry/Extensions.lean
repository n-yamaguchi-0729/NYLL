/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.Set
public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawExtension
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawIsGreatestOpensDifferenceExtension
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawOpensDiagonalDifferenceExtension
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.RationalMapSpecializesKrullDimensionLeOne
public import Nyll.SchemeTheory.LocalGeometry.OpenIrreducibleComponents
public import Nyll.SchemeTheory.LocalGeometry.SmoothNormalStalk
public import Nyll.SchemeTheory.RingTheory.RegularLocal.CohenMacaulay
public import Nyll.SchemeTheory.RingTheory.RegularLocal.LocalRingIsCohenMacaulayOfDimKrullDimensionQuotientAddHeight
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDepth
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalSpanFinrankKerAddKrullDimensionEq

/-!
# Extending group-valued morphisms over a DVR

A diagonal difference extension descends to the full smooth source. Rational maps and
regular local stalks provide the maximal difference domain and its diagonal neighborhoods.
The underlying open-domain and Krull-dimension constructions reuse their existing owners.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.DifferenceDescent

universe u

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

namespace Descent

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense
open GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DESC
  (Zop Zop_le_W Zop_le_snd pZ pZ_def aZ aZ_ι cZ cZ_ι
    aZ_fst aZ_snd tZ tZ_eq dZ vZ rZ rZ_base comp_rZ_eq_of_fst)

section Main

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  (t : T ⟶ Spec (CommRingCat.of R))
  (V : T.Opens)
  (W : (pullback t t).Opens)

scoped instance pZ_smooth [Smooth t] : Smooth (pZ t V W) := by
  rw [pZ_def]; infer_instance

theorem pZ_surjective [Smooth t]
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
        x.1 ∈ V)
    (hW : ∀ x : T, (pullback.diagonal t).base x ∈ W) :
    Function.Surjective (pZ t V W).base := by
  intro x
  obtain ⟨ξ, hξV, hξt, hξx⟩ : ∃ ξ : T, ξ ∈ V ∧ t.base ξ = t.base x ∧ ξ ⤳ x := by
    by_cases hx : t.base x = IsLocalRing.closedPoint R
    · let S := {y : T // t.base y = IsLocalRing.closedPoint R}
      have hSc : IsClosed {y : T | t.base y = IsLocalRing.closedPoint R} :=
        (IsLocalRing.isClosed_singleton_closedPoint R).preimage (Scheme.Hom.continuous t)
      have : QuasiSober S := hSc.isClosedEmbedding_subtypeVal.quasiSober
      let x' : S := ⟨x, hx⟩
      have hC : irreducibleComponent x' ∈ irreducibleComponents S :=
        irreducibleComponent_mem_irreducibleComponents x'
      obtain ⟨ξ', hξ'⟩ : ∃ ξ' : S, IsGenericPoint ξ' (irreducibleComponent x') :=
        QuasiSober.sober isIrreducible_irreducibleComponent isClosed_irreducibleComponent
      obtain ⟨z, hzC, hzV⟩ := hVs _ hC
      have hUo : IsOpen {y : S | y.1 ∈ V} := V.2.preimage continuous_subtype_val
      have hξ'V : ξ' ∈ {y : S | y.1 ∈ V} := (hξ'.mem_open_set_iff hUo).mpr ⟨z, hzC, hzV⟩
      refine ⟨ξ'.1, hξ'V, by rw [ξ'.2, hx], ?_⟩
      exact (hξ'.specializes mem_irreducibleComponent).map continuous_subtype_val
    · exact ⟨x, hVη x hx, rfl, specializes_rfl⟩
  set s₀ := t.base x with hs₀
  let ιs := t.fiberι s₀
  let πs := t.fiberToSpecResidueField s₀
  let jx : Spec (T.residueField x) ⟶ Spec ((Spec (CommRingCat.of R)).residueField s₀) :=
    Spec.map (t.residueFieldMap x)
  have : Flat jx := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (t.residueFieldMap x).hom.Flat
    unfold RingHom.Flat
    let : Algebra ((Spec (CommRingCat.of R)).residueField s₀) (T.residueField x) :=
      (t.residueFieldMap x).hom.toAlgebra
    infer_instance
  have hnat : T.fromSpecResidueField x ≫ t = jx ≫ (Spec
      (CommRingCat.of R)).fromSpecResidueField s₀ :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField t x).symm
  let l : Spec (T.residueField x) ⟶ t.fiber s₀ := pullback.lift (T.fromSpecResidueField x) jx hnat
  have hl : l ≫ ιs = T.fromSpecResidueField x := pullback.lift_fst _ _ _
  have hl' : l ≫ πs = jx := pullback.lift_snd _ _ _
  let F := pullback πs jx
  let pr : F ⟶ t.fiber s₀ := pullback.fst πs jx
  have hm : (pullback.snd πs jx ≫ T.fromSpecResidueField x) ≫ t = (pr ≫ ιs) ≫ t := by
    rw [Category.assoc, hnat, ← pullback.condition_assoc, Category.assoc]
    exact (congrArg (fun k => pr ≫ k) (pullback.condition (f := t)
      (g := (Spec (CommRingCat.of R)).fromSpecResidueField s₀))).symm
  let m : F ⟶ pullback t t := pullback.lift (pullback.snd πs jx ≫ T.fromSpecResidueField x) (pr ≫
      ιs) hm
  have hm1 : m ≫ pullback.fst t t = pullback.snd πs jx ≫ T.fromSpecResidueField x :=
      pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd t t = pr ≫ ιs := pullback.lift_snd _ _ _
  let σ : Spec (T.residueField x) ⟶ F := pullback.lift l (𝟙 _) (by rw [hl', Category.id_comp])
  have hσm : σ ≫ m = T.fromSpecResidueField x ≫ pullback.diagonal t := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        Category.assoc,
        pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, hm2, ← Category.assoc, pullback.lift_fst, hl, Category.assoc,
        pullback.diagonal_snd, Category.comp_id]
  have hσpr : σ ≫ pr ≫ ιs = T.fromSpecResidueField x := by
    rw [← Category.assoc, pullback.lift_fst, hl]
  let pt : Spec (T.residueField x) := IsLocalRing.closedPoint (T.residueField x)
  have hpt : (T.fromSpecResidueField x).base pt = x := Scheme.fromSpecResidueField_apply x pt
  let φ₀ : F := σ.base pt
  have hφ₀W : m.base φ₀ ∈ W := by
    have : m.base φ₀ = (pullback.diagonal t).base x := by
      rw [← hpt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσm]
    rw [this]; exact hW x
  have hy₀ : ιs.base (pr.base φ₀) = x := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσpr, hpt]
  obtain ⟨yξ, hyξ⟩ : ξ ∈ Set.range ιs.base := by
    rw [Scheme.Hom.range_fiberι]; exact hξt
  have hspec : yξ ⤳ pr.base φ₀ := by
    rw [← (IsPreimmersion.isEmbedding ιs).isInducing.specializes_iff, hyξ, hy₀]
    exact hξx
  obtain ⟨φ₁, hφ₁, hprφ₁⟩ := Flat.generalizingMap pr hspec
  have hwW : m.base φ₁ ∈ W := (hφ₁.map (Scheme.Hom.continuous m)).mem_open W.2 hφ₀W
  have hwsnd : (pullback.snd t t).base (m.base φ₁) = ξ := by
    rw [← Scheme.Hom.comp_apply, hm2, Scheme.Hom.comp_apply, hprφ₁, hyξ]
  have hwfst : (pullback.fst t t).base (m.base φ₁) = x := by
    rw [← Scheme.Hom.comp_apply, hm1, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  have hwZ : m.base φ₁ ∈ Zop t V W := by
    rw [Zop, TopologicalSpace.Opens.mem_inf]
    exact ⟨hwW, by rw [Scheme.Hom.mem_preimage, hwsnd]; exact hξV⟩
  refine ⟨(⟨m.base φ₁, hwZ⟩ : (Zop t V W : Scheme.{u})), ?_⟩
  exact hwfst

theorem isReduced_kernelPair [Smooth t] :
    IsReduced (pullback (pZ t V W) (pZ t V W))  :=
  Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W ≫ t)

theorem dense_kernelPair_fstV [Smooth t]
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) :
    Dense (((pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W) ⁻¹ᵁ V : (pullback (pZ t V W)
        (pZ t V W)).Opens) :
      Set ↥(pullback (pZ t V W) (pZ t V W))) := by
  intro k
  let g := pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W ≫ t
  have : Flat g := inferInstance
  let η : ↥(Spec (CommRingCat.of R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hη : η ⤳ g.base k :=
    (PrimeSpectrum.le_iff_specializes (x := η) (y := g.base k)).mp bot_le
  obtain ⟨k', hk', hgk'⟩ := Flat.generalizingMap g hη
  have hne : η ≠ IsLocalRing.closedPoint R := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field R (by exact this.symm)
  have hk'V : k' ∈ ((pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W) ⁻¹ᵁ V) := by
    rw [Scheme.Hom.mem_preimage]
    apply hVη
    rw [← Scheme.Hom.comp_apply]
    change g.base k' ≠ _
    rw [hgk']; exact hne
  exact closure_mono (Set.singleton_subset_iff.mpr hk'V) hk'.mem_closure

end Main

theorem main
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
        x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hd : (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by
              rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by
            rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 := by
  set p := pZ t V W with hp
  set r := rZ G t V v W d with hr
  have hsurj : Function.Surjective p.base := pZ_surjective R t V W hVη hVs hd.1
  have : Surjective p := ⟨hsurj⟩
  let K := pullback p p
  have hcompat : pullback.fst p p ≫ r.1 = pullback.snd p p ≫ r.1 := by
    have : IsReduced K := isReduced_kernelPair R t V W
    let KV : K.Opens := (pullback.fst p p ≫ p) ⁻¹ᵁ V
    have : IsDominant KV.ι := by
      rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
      exact dense_kernelPair_fstV R t V W hVη
    have hfg : (pullback.fst p p ≫ r.1) ≫ f = (pullback.snd p p ≫ r.1) ≫ f := by
      rw [Category.assoc, Category.assoc, hr, rZ_base, ← hp, pullback.condition_assoc]
    refine ext_of_isDominant_of_isSeparated f hfg KV.ι ?_
    let b : (KV : Scheme.{u}) ⟶ (V : Scheme.{u}) := (pullback.fst p p ≫ p).resLE V KV le_rfl
    have hb : b ≫ V.ι = KV.ι ≫ pullback.fst p p ≫ p := Scheme.Hom.resLE_comp_ι _ _
    have h1 : (KV.ι ≫ pullback.fst p p) ≫ r.1 = b ≫ v.1 :=
      comp_rZ_eq_of_fst G t V v W d hd.2 _ b (by rw [hb, Category.assoc])
    have h2 : (KV.ι ≫ pullback.snd p p) ≫ r.1 = b ≫ v.1 :=
      comp_rZ_eq_of_fst G t V v W d hd.2 _ b (by rw [hb, Category.assoc, ← pullback.condition])
    rw [← Category.assoc, ← Category.assoc, h1, h2]
  have hmem : Sieve.generate (Presieve.singleton p) ∈ Scheme.fppfTopology.{u} T := by
    have h := (Scheme.Hom.cover.{u, 0} (P := @Flat ⊓ @LocallyOfFinitePresentation) p
      ⟨inferInstance, inferInstance⟩).mem_grothendieckTopology
    dsimp only [Scheme.Hom.cover, Precoverage.ZeroHypercover.singleton,
        PreZeroHypercover.singleton] at h
    rw [Sieve.ofArrows, Presieve.ofArrows_pUnit] at h
    exact h
  have hSA : Presieve.IsSheaf Scheme.fppfTopology.{u} (yoneda.obj A) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hSB : Presieve.IsSheaf Scheme.fppfTopology.{u} (yoneda.obj (Spec (CommRingCat.of R))) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hsheafA : Presieve.IsSheafFor (yoneda.obj A) (Presieve.singleton p) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hSA _ hmem
  have hsheafB : Presieve.IsSheafFor (yoneda.obj (Spec (CommRingCat.of R)))
      (Presieve.singleton p) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hSB _ hmem
  rw [Presieve.isSheafFor_singleton] at hsheafA hsheafB
  have hcompat' : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ ↑(Zop t V W)), p₁ ≫ p = p₂ ≫ p →
      (yoneda.obj A).map p₁.op r.1 = (yoneda.obj A).map p₂.op r.1 := by
    intro Z p₁ p₂ h12
    change p₁ ≫ r.1 = p₂ ≫ r.1
    rw [← pullback.lift_fst p₁ p₂ h12, Category.assoc, hcompat, ← Category.assoc, pullback.lift_snd]
  obtain ⟨φ₁, hφ₁, huniq⟩ := hsheafA r.1 hcompat'
  change p ≫ φ₁ = r.1 at hφ₁
  have hover : φ₁ ≫ f = t := by
    have hcB : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ ↑(Zop t V W)), p₁ ≫ p = p₂ ≫ p →
        (yoneda.obj (Spec (CommRingCat.of R))).map p₁.op (p ≫ t) =
          (yoneda.obj (Spec (CommRingCat.of R))).map p₂.op (p ≫ t) := by
      intro Z p₁ p₂ h12
      change p₁ ≫ p ≫ t = p₂ ≫ p ≫ t
      rw [← Category.assoc, h12, Category.assoc]
    obtain ⟨ψ, hψ, hψuniq⟩ := hsheafB (p ≫ t) hcB
    have e1 : φ₁ ≫ f = ψ := hψuniq (φ₁ ≫ f) (by
      change p ≫ φ₁ ≫ f = p ≫ t
      rw [← Category.assoc, hφ₁, hr, rZ_base])
    have e2 : t = ψ := hψuniq t rfl
    rw [e1, ← e2]
  refine ⟨⟨φ₁, hover⟩, ?_⟩
  let e : (V : Scheme.{u}) ⟶ pullback t t := pullback.lift V.ι V.ι rfl
  have he : e = V.ι ≫ pullback.diagonal t := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have herange : Set.range e.base ⊆ Set.range (Zop t V W).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change e.base y ∈ Zop t V W
    rw [Zop, TopologicalSpace.Opens.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [he, Scheme.Hom.comp_apply]; exact hd.1 _
    · rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_snd]; exact y.2
  let δ : (V : Scheme.{u}) ⟶ ↑(Zop t V W) := IsOpenImmersion.lift (Zop t V W).ι e herange
  have hδ : δ ≫ (Zop t V W).ι = e := IsOpenImmersion.lift_fac _ _ _
  have hδp : δ ≫ p = 𝟙 _ ≫ V.ι := by
    rw [hp, pZ_def, ← Category.assoc, hδ, pullback.lift_fst, Category.id_comp]
  have hrec := comp_rZ_eq_of_fst G t V v W d hd.2 δ (𝟙 _) hδp
  rw [Category.id_comp] at hrec
  have hδp' : δ ≫ p = V.ι := by rw [hδp, Category.id_comp]
  change V.ι ≫ φ₁ = v.1
  calc V.ι ≫ φ₁ = (δ ≫ p) ≫ φ₁ := by rw [hδp']
    _ = δ ≫ r.1 := by rw [Category.assoc, hφ₁]
    _ = v.1 := hrec

end Descent

end

end AbelianVarieties.NOSProofs.DifferenceDescent

namespace GoodReductionJacobian.RelativeGroupLaw

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.DifferenceDescent

theorem exists_extension_of_diagonal_difference_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
        x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hd : (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by
              rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by
            rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 :=
  Descent.main R G t V hVη hVs v W d hd

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.MaximalDifferenceDomain

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense
open GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM
  (exists_glue_of_eq_on_dense)

open GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DOM
  (prodOpen mem_prodOpen_iff prFst prSnd bD_ι cD_ι pt₁ pt₂ diffMap recovery_core)

noncomputable section
namespace DifferenceDomain
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.TopologicalSpace
open _root_.Topology

section Main2
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {T : Scheme.{u}}

theorem dense_of_generic_fibre_subset (t : T ⟶ Spec (CommRingCat.of R)) [Flat t] (V : T.Opens)
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) : Dense (V : Set T) := by
  intro x
  by_cases hx : t.base x ≠ IsLocalRing.closedPoint R
  · exact subset_closure (hVη x hx)
  · push Not at hx
    let η : ↥(Spec (CommRingCat.of R)) := (⊥ : PrimeSpectrum R)
    have hη : η ⤳ t.base x := (PrimeSpectrum.le_iff_specializes η (t.base x)).mp bot_le
    obtain ⟨x', hx'x, hx'η⟩ := Flat.generalizingMap t hη
    have hne : t.base x' ≠ IsLocalRing.closedPoint R := by
      intro h
      apply IsDiscreteValuationRing.not_a_field R
      have h2 : (η : PrimeSpectrum R).asIdeal = (IsLocalRing.closedPoint R).asIdeal := by
        rw [← h]; exact congrArg PrimeSpectrum.asIdeal hx'η.symm
      exact h2.symm
    exact closure_mono (Set.singleton_subset_iff.mpr (hVη x' hne))
        (specializes_iff_mem_closure.mp hx'x)

theorem dense_prodOpen (t : T ⟶ Spec (CommRingCat.of R)) [Flat t] [UniversallyOpen t] (V : T.Opens)
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) :
    Dense ((prodOpen t V : (pullback t t).Opens) : Set ↑(pullback t t)) := by
  have hV := dense_of_generic_fibre_subset t V hVη
  have h1 : IsOpenMap (pullback.fst t t).base := Scheme.Hom.isOpenMap (pullback.fst t t)
  have h2 : IsOpenMap (pullback.snd t t).base := Scheme.Hom.isOpenMap (pullback.snd t t)
  exact (hV.preimage h1).inter_of_isOpen_left (hV.preimage h2) ((pullback.fst t t) ⁻¹ᵁ V).2

theorem isReduced_pullback (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] : IsReduced
    (pullback t t)  :=
  Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.fst t t ≫ t)

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem isSeparated_of_isSeparated_over (f : A ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] : A.IsSeparated := by
  constructor
  rw [← terminal.comp_from f]
  infer_instance

theorem mem_opens_of_base {X : Scheme.{u}} (U : X.Opens) (y : ↑U) : U.ι.base y ∈ U := by
  have h : U.ι.base y ∈ Set.range U.ι.base := ⟨y, rfl⟩
  rwa [Scheme.Opens.range_ι] at h

theorem main (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ p : ↑(pullback t t), (pullback.fst t t).base p ∈ V → (pullback.snd t t).base p ∈ V →
          p ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by
              rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by
            rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) ∧
      (∀ (W' : (pullback t t).Opens) (d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f)
        (W₀ : (pullback t t).Opens) (h₀ : W₀ ≤ W ⊓ W'),
        ((W' : Set ↑(pullback t t)) ⊆ closure (W₀ : Set ↑(pullback t t))) →
        (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 = (pullback t t).homOfLE
            (h₀.trans inf_le_right) ≫ d'.1 →
        W' ≤ W ∧ ∀ (S : Scheme.{u}) (a' : S ⟶ ↑W') (a : S ⟶ ↑W), a' ≫ W'.ι = a ≫ W.ι →
            a' ≫ d'.1 = a ≫ d.1) := by
  have : IsReduced (pullback t t) := isReduced_pullback t
  have : A.IsSeparated := isSeparated_of_isSeparated_over f
  let : (pullback t t).Over (Spec (CommRingCat.of R)) := ⟨pullback.fst t t ≫ t⟩
  let : A.Over (Spec (CommRingCat.of R)) := ⟨f⟩
  have hDd : Dense ((prodOpen t V : (pullback t t).Opens) : Set ↑(pullback t t)) :=
      dense_prodOpen t V hVη
  let pΦ : (pullback t t).PartialMap A := ⟨prodOpen t V, hDd, (diffMap G t V v).1⟩
  have hpΦ : pΦ.IsOver (Spec (CommRingCat.of R)) := by
    rw [Scheme.PartialMap.isOver_iff, Scheme.PartialMap.compHom_hom]
    exact (diffMap G t V v).2
  let u := pΦ.toRationalMap
  have hu : u.IsOver (Spec (CommRingCat.of R)) := ⟨⟨pΦ, hpΦ, rfl⟩⟩
  let dW := u.toPartialMap
  have hdWover : dW.IsOver (Spec (CommRingCat.of R)) :=
    Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated.mp
      (by rw [Scheme.RationalMap.toRationalMap_toPartialMap]; exact hu)
  have hdW : dW.hom ≫ f = dW.domain.ι ≫ pullback.fst t t ≫ t := by
    have h := Scheme.PartialMap.isOver_iff.mp hdWover
    rwa [Scheme.PartialMap.compHom_hom] at h
  have hDW : prodOpen t V ≤ u.domain := pΦ.le_domain_toRationalMap
  have hres : (pullback t t).homOfLE hDW ≫ dW.hom = (diffMap G t V v).1 := by
    exact Scheme.PartialMap.toPartialMap_toRationalMap_restrict pΦ
  refine ⟨u.domain, ⟨dW.hom, hdW⟩, ?_, ?_, ?_⟩
  · intro p h1 h2
    exact hDW (show p ∈ prodOpen t V from ⟨h1, h2⟩)
  · intro S a b c hb hc
    have hrange : Set.range (a ≫ u.domain.ι).base ⊆ Set.range (prodOpen t V).ι.base := by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (a ≫ u.domain.ι).base s ∈ prodOpen t V
      rw [mem_prodOpen_iff]
      constructor
      · have e : (pullback.fst t t).base (u.domain.ι.base (a.base s)) = V.ι.base (b.base s) := by
          have e0 := congrArg (fun k => k.base s) hb
          simpa only [Scheme.Hom.comp_apply] using e0
        change (pullback.fst t t).base (u.domain.ι.base (a.base s)) ∈ V
        rw [e]; exact mem_opens_of_base V _
      · have e : (pullback.snd t t).base (u.domain.ι.base (a.base s)) = V.ι.base (c.base s) := by
          have e0 := congrArg (fun k => k.base s) hc
          simpa only [Scheme.Hom.comp_apply] using e0
        change (pullback.snd t t).base (u.domain.ι.base (a.base s)) ∈ V
        rw [e]; exact mem_opens_of_base V _
    let a' := IsOpenImmersion.lift (prodOpen t V).ι (a ≫ u.domain.ι) hrange
    have ha' : a' ≫ (prodOpen t V).ι = a ≫ u.domain.ι := IsOpenImmersion.lift_fac _ _ _
    have haa : a' ≫ (pullback t t).homOfLE hDW = a := by
      rw [← cancel_mono u.domain.ι, Category.assoc, Scheme.homOfLE_ι, ha']
    refine recovery_core G t V v _ _ _ _ a' b c ?_ ?_ rfl rfl ?_ ?_
    · rw [← Category.assoc a', ha', Category.assoc]
    · change a ≫ dW.hom = a' ≫ (diffMap G t V v).1
      calc a ≫ dW.hom = (a' ≫ (pullback t t).homOfLE hDW) ≫ dW.hom :=
            congrArg (fun c => c ≫ dW.hom) haa.symm
        _ = a' ≫ ((pullback t t).homOfLE hDW ≫ dW.hom) := Category.assoc _ _ _
        _ = a' ≫ (diffMap G t V v).1 := congrArg (fun c => a' ≫ c) hres
    · rw [← cancel_mono V.ι, Category.assoc, bD_ι, ← Category.assoc, ha', Category.assoc]
      exact hb
    · rw [← cancel_mono V.ι, Category.assoc, cD_ι, ← Category.assoc, ha', Category.assoc]
      exact hc
  · intro W' d' W₀ h₀ hcl hagree
    have hdense' : ((u.domain ⊓ W' : (pullback t t).Opens) : Set ↑(pullback t t)) ⊆ closure
        (W₀ : Set _) :=
      fun p hp => hcl hp.2
    obtain ⟨g, hg₁, hg₂⟩ := exists_glue_of_eq_on_dense
      (pullback.fst t t ≫ t) f u.domain W' dW.hom d'.1 hdW d'.2 W₀ h₀ hdense' hagree
    have hDsup : prodOpen t V ≤ u.domain ⊔ W' := hDW.trans le_sup_left
    let q : (pullback t t).PartialMap A := ⟨u.domain ⊔ W', hDd.mono (fun p hp => hDsup hp), g⟩
    have hq : q.toRationalMap = u := by
      rw [show u = pΦ.toRationalMap from rfl, Scheme.PartialMap.toRationalMap_eq_iff]
      refine ⟨prodOpen t V, hDd, hDsup, le_rfl, ?_⟩
      rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom]
      change (pullback t t).homOfLE hDsup ≫ g = (pullback t t).homOfLE le_rfl ≫ (diffMap G t V v).1
      rw [← hres, ← hg₁]
      simp only [← Category.assoc, Scheme.homOfLE_homOfLE]
    have hle : u.domain ⊔ W' ≤ u.domain := by
      have h := q.le_domain_toRationalMap
      rwa [hq] at h
    refine ⟨le_sup_right.trans hle, ?_⟩
    intro S a' a haa'
    have e : a' ≫ (pullback t t).homOfLE (le_sup_right : W' ≤ u.domain ⊔ W') =
        a ≫ (pullback t t).homOfLE (le_sup_left : u.domain ≤ u.domain ⊔ W') := by
      rw [← cancel_mono (u.domain ⊔ W').ι, Category.assoc, Scheme.homOfLE_ι, Category.assoc,
          Scheme.homOfLE_ι]
      exact haa'
    change a' ≫ d'.1 = a ≫ dW.hom
    rw [← hg₂, ← hg₁, ← Category.assoc, e, Category.assoc]

end Main2
end DifferenceDomain
end

end AbelianVarieties.NOSProofs.MaximalDifferenceDomain

namespace GoodReductionJacobian.RelativeGroupLaw

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.MaximalDifferenceDomain

theorem exists_isGreatest_opens_difference_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (_hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
        x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ p : ↑(pullback t t), (pullback.fst t t).base p ∈ V → (pullback.snd t t).base p ∈ V →
          p ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by
              rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by
            rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) ∧
      (∀ (W' : (pullback t t).Opens) (d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f)
        (W₀ : (pullback t t).Opens) (h₀ : W₀ ≤ W ⊓ W'),
        ((W' : Set ↑(pullback t t)) ⊆ closure (W₀ : Set ↑(pullback t t))) →
        (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 = (pullback t t).homOfLE
            (h₀.trans inf_le_right) ≫ d'.1 →
        W' ≤ W ∧ ∀ (S : Scheme.{u}) (a' : S ⟶ ↑W') (a : S ⟶ ↑W), a' ≫ W'.ι = a ≫ W.ι →
            a' ≫ d'.1 = a ≫ d.1) :=
  DifferenceDomain.main G t V hVη v

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.DiagonalDifferenceExtension

open AbelianVarieties.NOSProofs.MaximalDifferenceDomain

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
open GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG
  (exists_specializes_diagonal_of_ringKrullDim_le_one_of_quotient_add_height
    exists_nat_ringKrullDim_eq_of_isRegularLocalRing
    ringKrullDim_quotient_add_height_of_isRegularLocalRing
    dense_inf_preimage_of_dense)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Density

theorem isReduced_pullback_of_smooth {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] : IsReduced (pullback t t)  :=
  Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.fst t t ≫ t)

end Density

noncomputable section
namespace DiagonalUnit
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.TopologicalSpace
open _root_.Topology

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {A T : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)}

theorem isReduced_of_smooth (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] : IsReduced T  :=
  Smooth.isReduced_of_isReduced_of_isLocallyNoetherian t

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem eq_one_of_mul_eq (G : RelativeGroupLaw R f) {S : Scheme.{u}} (g : S ⟶ Spec
    (CommRingCat.of R))
    (x y : SchemeHomOver g f) (h : G.mul g x y = y) : x = G.one g := by
  calc x = G.mul g x (G.one g) := (G.mul_one g x).symm
    _ = G.mul g x (G.mul g y (G.inv g y)) := by rw [G.mul_inv_cancel]
    _ = G.mul g (G.mul g x y) (G.inv g y) := by rw [G.mul_assoc]
    _ = G.one g := by rw [h, G.mul_inv_cancel]

open GoodReductionJacobian.RelativeGroupLaw.WeilExtField.C3
  (isDominant_homOfLE_inf)

theorem diagonal_restrict_comp_eq_unit (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hV : Dense (V : Set T)) (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hrec : ∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by
              rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by
            rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) :
    (pullback.diagonal t ∣_ W) ≫ d.1 =
      ((pullback.diagonal t) ⁻¹ᵁ W).ι ≫ t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have : IsReduced T := isReduced_of_smooth t
  set U : T.Opens := (pullback.diagonal t) ⁻¹ᵁ W with hU
  have : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
  set e := G.one (𝟙 (Spec (CommRingCat.of R))) with he
  have hΔfst : (pullback.diagonal t ∣_ W) ≫ W.ι ≫ pullback.fst t t = U.ι := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
  have hΔsnd : (pullback.diagonal t ∣_ W) ≫ W.ι ≫ pullback.snd t t = U.ι := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, pullback.diagonal_snd,
        Category.comp_id]
  have hL : ((pullback.diagonal t ∣_ W) ≫ d.1) ≫ f = U.ι ≫ t := by
    rw [Category.assoc, d.2]
    simp only [← Category.assoc]
    rw [Category.assoc (pullback.diagonal t ∣_ W), hΔfst]
  have hR : (U.ι ≫ t ≫ e.1) ≫ f = U.ι ≫ t := by
    rw [Category.assoc, Category.assoc, e.2, Category.comp_id]
  have : IsDominant (T.homOfLE (inf_le_left : U ⊓ V ≤ U)) :=
    isDominant_homOfLE_inf U V hV
  refine ext_of_isDominant_of_isSeparated f (hL.trans hR.symm) (T.homOfLE (inf_le_left : U ⊓
      V ≤ U)) ?_
  set a : (U ⊓ V).toScheme ⟶ W.toScheme := T.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫
      (pullback.diagonal t ∣_ W) with ha
  set b : (U ⊓ V).toScheme ⟶ V.toScheme := T.homOfLE (inf_le_right : U ⊓ V ≤ V) with hb0
  have hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι := by
    rw [ha, Category.assoc, hΔfst, Scheme.homOfLE_ι, hb0, Scheme.homOfLE_ι]
  have hc : a ≫ W.ι ≫ pullback.snd t t = b ≫ V.ι := by
    rw [ha, Category.assoc, hΔsnd, Scheme.homOfLE_ι, hb0, Scheme.homOfLE_ι]
  have key := hrec _ a b b hb hc
  have hone := eq_one_of_mul_eq G _ _ _ key
  have h1 : a ≫ d.1 = (a ≫ W.ι ≫ pullback.fst t t ≫ t) ≫ e.1 := by
    have h2 := congrArg Subtype.val hone
    rw [← G.one_natural (𝟙 (Spec (CommRingCat.of R))) (a ≫ W.ι ≫ pullback.fst t t ≫ t)
      (a ≫ W.ι ≫ pullback.fst t t ≫ t) (Category.comp_id _)] at h2
    exact h2
  calc T.homOfLE _ ≫ (pullback.diagonal t ∣_ W) ≫ d.1 = a ≫ d.1 := by rw [ha, Category.assoc]
    _ = (a ≫ W.ι ≫ pullback.fst t t ≫ t) ≫ e.1 := h1
    _ = T.homOfLE _ ≫ U.ι ≫ t ≫ e.1 := by
        rw [ha]
        simp only [Category.assoc]
        rw [reassoc_of% hΔfst]

end DiagonalUnit
end

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.Topology

namespace AffineDifferenceMap

theorem exists_mem_specializes {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Flat t] (V : T.Opens)
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) (y : T) :
    ∃ θ : T, θ ∈ V ∧ θ ⤳ y := by
  let η : ↥(Spec (CommRingCat.of R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hη : η ⤳ t.base y := (PrimeSpectrum.le_iff_specializes (x := η) (y := t.base y)).mp bot_le
  obtain ⟨θ, hθ, htθ⟩ := Flat.generalizingMap t hη
  have hne : η ≠ IsLocalRing.closedPoint R := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field R (by exact this.symm)
  exact ⟨θ, hVη θ (by rw [htθ]; exact hne), hθ⟩

theorem exists_rationalMap_component_affine
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hVV : ∀ p : ↑(pullback t t), (pullback.fst t t).base p ∈ V → (pullback.snd t t).base p ∈ V →
        p ∈ W)
    (hrec : ∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by
              rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by
            rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)
    (hmax : ∀ (W' : (pullback t t).Opens) (d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f)
        (W₀ : (pullback t t).Opens) (h₀ : W₀ ≤ W ⊓ W'),
        ((W' : Set ↑(pullback t t)) ⊆ closure (W₀ : Set ↑(pullback t t))) →
        (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 = (pullback t t).homOfLE
            (h₀.trans inf_le_right) ≫ d'.1 →
        W' ≤ W ∧ ∀ (S : Scheme.{u}) (a' : S ⟶ ↑W') (a : S ⟶ ↑W), a' ≫ W'.ι = a ≫ W.ι →
            a' ≫ d'.1 = a ≫ d.1)
    (y : T) (P₀ : (pullback t t).Opens) [IrreducibleSpace (P₀ : Scheme.{u})]
    (hyP₀ : (pullback.diagonal t).base y ∈ P₀)
    (H : A.Opens) (hHe : ∀ s : ↥(Spec (CommRingCat.of R)),
        (G.one (𝟙 (Spec (CommRingCat.of R)))).1.base s ∈ H) :
    ∃ u : (P₀ : Scheme.{u}) ⤏ (H : Scheme.{u}),
      (∀ p : ↥P₀, p ∈ u.domain → P₀.ι.base p ∈ W) ∧
      (∀ ξ : T, ξ ∈ V → ξ ⤳ y →
        ∃ hξ : (pullback.diagonal t).base ξ ∈ P₀, (⟨(pullback.diagonal t).base ξ,
            hξ⟩ : ↥P₀) ∈ u.domain) := by
  classical
  have : IsReduced (pullback t t) := Density.isReduced_pullback_of_smooth t
  have hV : Dense (V : Set T) := DifferenceDomain.dense_of_generic_fibre_subset t V hVη
  have hC3a := DiagonalUnit.diagonal_restrict_comp_eq_unit G t V hV v W d hrec
  have hdΔ : ∀ (θ : T) (hθ : (pullback.diagonal t).base θ ∈ W),
      d.1.base ⟨(pullback.diagonal t).base θ, hθ⟩ ∈ H := by
    intro θ hθ
    have hθ' : θ ∈ (pullback.diagonal t) ⁻¹ᵁ W := by rw [Scheme.Hom.mem_preimage]; exact hθ
    have e1 : d.1 ((pullback.diagonal t ∣_ W)
        (⟨θ, hθ'⟩ : ((pullback.diagonal t ⁻¹ᵁ W) : Scheme.{u}))) =
        (G.one (𝟙 (Spec (CommRingCat.of R)))).1 (t θ) :=
      congrArg (fun φ : ((pullback.diagonal t ⁻¹ᵁ W) : Scheme.{u}) ⟶ A =>
        φ (⟨θ, hθ'⟩ : ((pullback.diagonal t ⁻¹ᵁ W) : Scheme.{u}))) hC3a
    have e2 : (pullback.diagonal t ∣_ W) (⟨θ, hθ'⟩ :
        ((pullback.diagonal t ⁻¹ᵁ W) : Scheme.{u})) =
        (⟨(pullback.diagonal t).base θ, hθ⟩ : (W : Scheme.{u})) :=
      Subtype.ext (morphismRestrict_base_coe _ _ _)
    have e3 : d.1 (⟨(pullback.diagonal t).base θ, hθ⟩ : (W : Scheme.{u})) =
        (G.one (𝟙 (Spec (CommRingCat.of R)))).1 (t θ) :=
      (congrArg (fun w : (W : Scheme.{u}) => d.1 w) e2).symm.trans e1
    exact e3.symm ▸ hHe (t θ)
  have key : ∀ θ : T, θ ∈ V → θ ⤳ y →
      (pullback.diagonal t).base θ ∈ P₀ ∧ (pullback.diagonal t).base θ ∈ W := by
    intro θ hθV hθy
    refine ⟨(hθy.map (Scheme.Hom.continuous (pullback.diagonal t))).mem_open P₀.2 hyP₀, hVV _ ?_ ?_⟩
    · rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]; exact hθV
    · rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]; exact hθV
  obtain ⟨θ₀, hθ₀V, hθ₀y⟩ := exists_mem_specializes t V hVη y
  let WH : (pullback t t).Opens := W.ι ''ᵁ (d.1 ⁻¹ᵁ H)
  have hWH_le : WH ≤ W := by
    rintro q ⟨w, -, rfl⟩; exact w.2
  let U₀ : (P₀ : Scheme.{u}).Opens := P₀.ι ⁻¹ᵁ WH
  have hrange1 : Set.range (U₀.ι ≫ P₀.ι).base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hWH_le ((Scheme.Hom.mem_preimage _).mp z.2)
  let ℓ := IsOpenImmersion.lift W.ι (U₀.ι ≫ P₀.ι) hrange1
  have hℓ : ℓ ≫ W.ι = U₀.ι ≫ P₀.ι := IsOpenImmersion.lift_fac _ _ _
  have hℓmem : ∀ z : (U₀ : Scheme.{u}), ℓ.base z ∈ d.1 ⁻¹ᵁ H := by
    intro z
    have hz : P₀.ι.base (U₀.ι.base z) ∈ WH := (Scheme.Hom.mem_preimage _).mp z.2
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = ℓ.base z := by
      apply W.ι.isOpenEmbedding.injective
      refine hwz.trans ?_
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hℓ]
    rw [← this]; exact hw
  have hrange2 : Set.range (ℓ ≫ d.1).base ⊆ Set.range H.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (Scheme.Hom.mem_preimage _).mp (hℓmem z)
  let rep : (U₀ : Scheme.{u}) ⟶ (H : Scheme.{u}) := IsOpenImmersion.lift H.ι (ℓ ≫ d.1) hrange2
  have hrep : rep ≫ H.ι = ℓ ≫ d.1 := IsOpenImmersion.lift_fac _ _ _
  have hΔU₀ : ∀ (θ : T) (hθV : θ ∈ V) (hθy : θ ⤳ y),
      (⟨(pullback.diagonal t).base θ, (key θ hθV hθy).1⟩ : ↥P₀) ∈ U₀ := by
    intro θ hθV hθy
    change P₀.ι.base _ ∈ WH
    exact ⟨⟨(pullback.diagonal t).base θ, (key θ hθV hθy).2⟩,
      (Scheme.Hom.mem_preimage _).mpr (hdΔ θ (key θ hθV hθy).2), rfl⟩
  have hU₀dense : Dense (SetLike.coe U₀) :=
    IsOpen.dense U₀.2 ⟨⟨(pullback.diagonal t).base θ₀, (key θ₀ hθ₀V hθ₀y).1⟩, hΔU₀ θ₀ hθ₀V hθ₀y⟩
  let g₀ : (P₀ : Scheme.{u}).PartialMap (H : Scheme.{u}) := ⟨U₀, hU₀dense, rep⟩
  refine ⟨g₀.toRationalMap, ?_, ?_⟩
  · intro p hp
    obtain ⟨g, hpg, hgeq⟩ := Scheme.RationalMap.mem_domain.mp hp
    rw [Scheme.PartialMap.toRationalMap_eq_iff] at hgeq
    obtain ⟨W₀, hW₀d, hW₀g, hW₀g₀, hagree⟩ := hgeq
    rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom] at hagree
    change (P₀ : Scheme.{u}).homOfLE hW₀g ≫ g.hom = (P₀ : Scheme.{u}).homOfLE hW₀g₀ ≫ rep at hagree
    have : IsDominant ((P₀ : Scheme.{u}).homOfLE hW₀g) :=
      AlgebraicGeometry.Opens.isDominant_homOfLE hW₀d hW₀g
    have hℓR : ℓ ≫ d.1 ≫ f = U₀.ι ≫ P₀.ι ≫ pullback.fst t t ≫ t := by
      rw [d.2, ← Category.assoc, hℓ, Category.assoc]
    have hgover : g.hom ≫ H.ι ≫ f = g.domain.ι ≫ P₀.ι ≫ pullback.fst t t ≫ t := by
      refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _)
        ((P₀ : Scheme.{u}).homOfLE hW₀g) ?_
      rw [← Category.assoc, hagree, Category.assoc, ← Category.assoc rep, hrep, Category.assoc, hℓR,
        ← Category.assoc, Scheme.homOfLE_ι, ← Category.assoc ((P₀ : Scheme.{u}).homOfLE hW₀g),
            Scheme.homOfLE_ι]
    let W' : (pullback t t).Opens := P₀.ι ''ᵁ g.domain
    let iso := Scheme.Hom.isoImage P₀.ι g.domain
    let d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f :=
      ⟨iso.inv ≫ g.hom ≫ H.ι, by
        rw [Category.assoc, Category.assoc, hgover, ← Category.assoc iso.inv,
          ← Category.assoc (iso.inv ≫ g.domain.ι), Category.assoc iso.inv,
              Scheme.Hom.isoImage_inv_ι]⟩
    let W₀' : (pullback t t).Opens := P₀.ι ''ᵁ W₀
    have hW₀'W : W₀' ≤ W := by
      rintro _ ⟨q, hq, rfl⟩
      exact hWH_le ((Scheme.Hom.mem_preimage _).mp (hW₀g₀ hq))
    have hW₀'W' : W₀' ≤ W' := by
      rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hW₀g hq, rfl⟩
    have h₀ : W₀' ≤ W ⊓ W' := le_inf hW₀'W hW₀'W'
    have hdense' : ((W' : (pullback t t).Opens) : Set ↑(pullback t t)) ⊆ closure
        (W₀' : Set ↑(pullback t t)) := by
      rintro _ ⟨q, -, rfl⟩
      have hq : q ∈ closure (SetLike.coe W₀) := hW₀d q
      have := image_closure_subset_closure_image (Scheme.Hom.continuous P₀.ι) ⟨q, hq, rfl⟩
      rwa [← Scheme.Hom.coe_image] at this
    have hagree' : (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 =
        (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ d'.1 := by
      let j := Scheme.Hom.isoImage P₀.ι W₀
      rw [← cancel_epi j.hom]
      have hL : j.hom ≫ (pullback t t).homOfLE (h₀.trans inf_le_left) =
          (P₀ : Scheme.{u}).homOfLE hW₀g₀ ≫ ℓ := by
        rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι,
            Category.assoc, hℓ,
          ← Category.assoc, Scheme.homOfLE_ι]
      have hR : j.hom ≫ (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ iso.inv =
          (P₀ : Scheme.{u}).homOfLE hW₀g := by
        rw [← cancel_mono (g.domain.ι ≫ P₀.ι), Category.assoc, Category.assoc,
            Scheme.Hom.isoImage_inv_ι,
          Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι, ← Category.assoc, Scheme.homOfLE_ι]
      rw [← Category.assoc, hL, Category.assoc, ← hrep, ← Category.assoc, ← hagree, Category.assoc]
      change _ = j.hom ≫ (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ iso.inv ≫ g.hom ≫ H.ι
      rw [← Category.assoc j.hom, ← Category.assoc (j.hom ≫ _), Category.assoc j.hom, hR]
    obtain ⟨hW'W, -⟩ := hmax W' d' W₀' h₀ hdense' hagree'
    exact hW'W ⟨p, hpg, rfl⟩
  · intro ξ hξV hξy
    exact ⟨(key ξ hξV hξy).1, g₀.le_domain_toRationalMap (hΔU₀ ξ hξV hξy)⟩

end AffineDifferenceMap

namespace DiagonalDimension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem bprime_inputs
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (y : T) :
    ∃ nA : ℕ, ringKrullDim ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) = nA ∧
      (∀ 𝔔 : Ideal ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)), 𝔔.IsPrime →
        ringKrullDim (((pullback t t).presheaf.stalk
            ((pullback.diagonal t).base y)) ⧸ 𝔔) + 𝔔.height = nA) ∧
      ((RingHom.ker ((pullback.diagonal t).stalkMap y).hom).spanFinrank : WithBot ℕ∞)
          + ringKrullDim (T.presheaf.stalk y)
        = ringKrullDim ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) := by
  have hregP : IsRegularLocalRing ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing R
        (pullback.fst t t ≫ t) _
  have hregT : IsRegularLocalRing (T.presheaf.stalk y) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing R t y
  obtain ⟨nA, hA⟩ := exists_nat_ringKrullDim_eq_of_isRegularLocalRing
    ((pullback t t).presheaf.stalk ((pullback.diagonal t).base y))
  refine ⟨nA, hA, ringKrullDim_quotient_add_height_of_isRegularLocalRing _ nA hA, ?_⟩
  exact IsRegularLocalRing.spanFinrank_ker_add_ringKrullDim_eq
      ((pullback.diagonal t).stalkMap y).hom
    ((pullback.diagonal t).stalkMap_surjective y)

end DiagonalDimension

open GoodReductionJacobian.RelativeGroupLaw.WeilExtField.DIAG.B
  (isIntegral_and_isLocallyNoetherian_and_isIntegrallyClosed_of_isIrreducible
    exists_isAffineOpen_forall_mem_of_isLocalRing
    specializes_ι_of_specializes specializes_of_specializes_ι ringKrullDim_stalk_ι
    ι_base_apply_mk)

namespace DiagonalDimension

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.Topology

theorem diag_assembly
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [Smooth f]
        [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
        x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by
              rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by
            rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) := by
  classical
  obtain ⟨W, d, hVV, hrec, hmax⟩ :=
    _root_.GoodReductionJacobian.RelativeGroupLaw.exists_isGreatest_opens_difference_extension
      R G t V hVη hVs v
  refine ⟨W, d, ?_, hrec⟩
  intro y
  by_contra hy
  set q : ↑(pullback t t) := (pullback.diagonal t).base y with hq_def
  have : IsNoetherianRing R := inferInstance
  have hTln : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have hPln : IsLocallyNoetherian (pullback t t) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst t t ≫ t)
  have hPn : ∀ p : ↑(pullback t t), IsDomain ((pullback t t).presheaf.stalk p) ∧
      IsIntegrallyClosed ((pullback t t).presheaf.stalk p) := fun p =>
    AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst t t ≫ t) p
  obtain ⟨hP₀open, hP₀uniq⟩ :=
    AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk (X :=
        pullback t t) (fun p => (hPn p).1) q
  set P₀ : (pullback t t).Opens := ⟨irreducibleComponent q, hP₀open⟩ with hP₀_def
  have hqP₀ : q ∈ P₀ := mem_irreducibleComponent
  obtain ⟨hP₀int, hP₀ln, hP₀n⟩ :=
    isIntegral_and_isLocallyNoetherian_and_isIntegrallyClosed_of_isIrreducible hPn P₀
      (isIrreducible_irreducibleComponent (x := q))
  have : IsIntegral (P₀ : Scheme.{u}) := hP₀int
  have : IsLocallyNoetherian (P₀ : Scheme.{u}) := hP₀ln
  obtain ⟨H, hHaff, hHe⟩ := exists_isAffineOpen_forall_mem_of_isLocalRing
    (G.one (𝟙 (Spec (CommRingCat.of R)))).1
  have : IsAffine (H : Scheme.{u}) := hHaff
  obtain ⟨u, hu_dom_le_W, hu_diag⟩ :=
    AffineDifferenceMap.exists_rationalMap_component_affine
      G t V hVη v W d hVV hrec hmax y P₀ hqP₀ H hHe
  have hq_dom : (⟨q, hqP₀⟩ : ↥P₀) ∉ u.domain := by
    intro h
    have h' := hu_dom_le_W _ h
    rw [ι_base_apply_mk] at h'
    exact hy h'
  obtain ⟨z, hz_dom, hzq, hz_dim⟩ :=
    AlgebraicGeometry.Scheme.RationalMap.exists_specializes_ringKrullDim_le_one_of_not_mem_domain
      hP₀n u ⟨q, hqP₀⟩ hq_dom
  have hηq : P₀.ι.base z ⤳ q := by
    have h := specializes_ι_of_specializes P₀ hzq
    rwa [ι_base_apply_mk] at h
  have hη_dim : ringKrullDim ((pullback t t).presheaf.stalk (P₀.ι.base z)) ≤ 1 := by
    exact (ringKrullDim_stalk_ι P₀ z).trans_le hz_dim
  obtain ⟨nA, hA, hCM, hRS⟩ := DiagonalDimension.bprime_inputs R t y
  obtain ⟨ξ, hξy, hξ_dim, hzξ⟩ :=
    exists_specializes_diagonal_of_ringKrullDim_le_one_of_quotient_add_height t y nA hA hCM hRS
      (P₀.ι.base z) hηq hη_dim
  have hξV : ξ ∈ V :=
    AlgebraicGeometry.mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing
      R t V hVη hVs ξ hξ_dim
  obtain ⟨hξP₀, hξ_dom⟩ := hu_diag ξ hξV hξy
  refine hz_dom ?_
  have hzξ' : z ⤳ (⟨(pullback.diagonal t).base ξ, hξP₀⟩ : ↥P₀) := by
    refine specializes_of_specializes_ι P₀ ?_
    rw [ι_base_apply_mk]
    exact hzξ
  exact hzξ'.mem_open u.domain.2 hξ_dom

end DiagonalDimension

end AbelianVarieties.NOSProofs.DiagonalDifferenceExtension

namespace GoodReductionJacobian.RelativeGroupLaw

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.DiagonalDifferenceExtension

theorem exists_opens_diagonal_difference_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [Smooth f]
        [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
        x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by
              rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by
            rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) :=
  DiagonalDimension.diag_assembly R G t V hVη hVs v

end GoodReductionJacobian.RelativeGroupLaw
end

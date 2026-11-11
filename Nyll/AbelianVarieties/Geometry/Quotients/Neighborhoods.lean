/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.Choose
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AbelianVarieties.Geometry.PartialActions.Maximality
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.Affine.OpenNeighborhoods
public import Nyll.SchemeTheory.LocalGeometry.DVRLifts
public import Nyll.AbelianVarieties.Basic
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Action
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Affine neighborhoods for relative group quotients

Translation and specialization produce common neighborhoods, spread étaleness along
an action, and descend affine neighborhoods through finite flat covers.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_forall_mul_base_mem_of_forall_specializes_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.QuotientTranslationNeighborhoods

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Topology

universe u

namespace TranslationNeighborhoods

open GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)

open AbelianVarieties.NOSProofs.TranslationSpecialization.Specialization
  (rightMul comp_rightMul)

/-- Left translation after base change by a relative point. -/
noncomputable def leftMul {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (γ : SchemeHomOver t₀ g) : pullback g t₀ ⟶ B :=
  (LB.mul (pullback.snd g t₀ ≫ t₀) (schemeHomOverComp (pullback.snd g t₀) rfl γ)
      ⟨pullback.fst g t₀, pullback.condition⟩).1

theorem leftMul_comp_base {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (γ : SchemeHomOver t₀ g) : leftMul LB t₀ γ ≫ g = pullback.snd g t₀ ≫ t₀ :=
  (LB.mul _ _ _).2

theorem comp_leftMul {T₀ T : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (γ : SchemeHomOver t₀ g) (ψ : T ⟶ pullback g t₀) (t' : T ⟶ Spec (CommRingCat.of R))
    (hψ : ψ ≫ (pullback.snd g t₀ ≫ t₀) = t') :
    ψ ≫ leftMul LB t₀ γ =
      (LB.mul t' ⟨ψ ≫ pullback.snd g t₀ ≫ γ.1, by rw [Category.assoc, Category.assoc, γ.2, ←
        Category.assoc, ← hψ, Category.assoc]⟩
        ⟨ψ ≫ pullback.fst g t₀, by rw [Category.assoc, pullback.condition, ← Category.assoc, ← hψ,
          Category.assoc]⟩).1 := by
  have h := LB.mul_natural (pullback.snd g t₀ ≫ t₀) t' ψ hψ
    (schemeHomOverComp (pullback.snd g t₀) rfl γ) ⟨pullback.fst g t₀, pullback.condition⟩
  have h1 := congrArg Subtype.val h
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  unfold leftMul
  rw [h1]
  congr 2

section Main

variable [IsDomain R] [IsDiscreteValuationRing R] [Smooth g] [IsSeparated g] [QuasiCompact g]

/-- The image of points translated outside the chosen open. -/
def badSet (U : B.Opens) (s₀ : B) : Set B :=
  (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
    ((rightMul LB (B.fromSpecResidueField s₀ ≫ g) ⟨B.fromSpecResidueField s₀, rfl⟩).base ⁻¹' ((U :
      Set B)ᶜ))

theorem not_mem_closure_badSet (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure (badSet LB U s₀) :=
  not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
    LB U hU s₀ hs₀ η hηk hηmax

omit [IsDomain R] [IsDiscreteValuationRing R] [Smooth g] [IsSeparated g] [QuasiCompact g] in
theorem specializes_fiberι_iff (y : ↑(Spec (CommRingCat.of R))) (a b : ↑(g.fiber y)) :
    (g.fiberι y).base a ⤳ (g.fiberι y).base b ↔ a ⤳ b :=
  (g.fiberι y).isEmbedding.isInducing.specializes_iff

omit [IsDomain R] [IsDiscreteValuationRing R] [Smooth g] [IsSeparated g] [QuasiCompact g] in
theorem mem_range_fiberι_of_eq (y : ↑(Spec (CommRingCat.of R))) (b : B) (hb : g.base b = y) :
    ∃ b' : ↑(g.fiber y), (g.fiberι y).base b' = b := by
  have : b ∈ Set.range (g.fiberι y) := by rw [Scheme.Hom.range_fiberι]; exact hb
  exact this

omit [IsDomain R] [IsDiscreteValuationRing R] [Smooth g] [IsSeparated g] [QuasiCompact g] in
theorem base_fiberι (y : ↑(Spec (CommRingCat.of R))) (a : ↑(g.fiber y)) : g.base ((g.fiberι y).base
  a) = y := by
  have : (g.fiberι y).base a ∈ g ⁻¹' {y} := by rw [← Scheme.Hom.range_fiberι]; exact ⟨a, rfl⟩
  exact this

omit [IsDomain R] [IsDiscreteValuationRing R] [IsSeparated g] [QuasiCompact g] in
theorem exists_specializes_closedInFibre (s : B) :
    ∃ s₀ : B, s ⤳ s₀ ∧ ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀ := by
  let F := g.fiber (g.base s)
  have : LocallyOfFiniteType (g.fiberToSpecResidueField (g s)) :=
    MorphismProperty.of_isPullback
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback g
        ((Spec (CommRingCat.of R)).fromSpecResidueField (g s))) inferInstance
  have : JacobsonSpace F :=
    LocallyOfFiniteType.jacobsonSpace (g.fiberToSpecResidueField (g.base s))
  let s' : ↑F := g.asFiber s
  have hs' : (g.fiberι _).base s' = s := g.fiberι_asFiber s
  obtain ⟨c, hc, hcc⟩ := nonempty_inter_closedPoints (X := ↑F) (Z := closure {s'})
    ⟨s', subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  refine ⟨(g.fiberι _).base c, ?_, ?_⟩
  · have h := (specializes_fiberι_iff (g := g) _ s' c).mpr (specializes_iff_mem_closure.mpr hc)
    rwa [hs'] at h
  · intro y hy hgy
    rw [base_fiberι] at hgy
    obtain ⟨y', rfl⟩ := mem_range_fiberι_of_eq (g := g) _ y hgy
    replace hy : c ⤳ y' := (specializes_fiberι_iff (g := g) (g s) c y').mp hy
    have hc' : IsClosed ({c} : Set ↑F) := hcc
    have : y' ∈ ({c} : Set ↑F) := hy.mem_closed hc' rfl
    rw [Set.mem_singleton_iff.mp this]

include LB in
omit [Smooth g] [IsSeparated g] [QuasiCompact g] in
theorem exists_maximal_specialFibre :
    ∃ η : B, g.base η = IsLocalRing.closedPoint R ∧
      ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η := by
  let e : Spec (CommRingCat.of R) ⟶ B := (LB.one (𝟙 _)).1
  have he : e ≫ g = 𝟙 _ := (LB.one (𝟙 _)).2
  let p : B := e.base (IsLocalRing.closedPoint R)
  have hp : g.base p = IsLocalRing.closedPoint R := by
    change (e ≫ g) (IsLocalRing.closedPoint R) = _
    rw [he]; rfl
  let F := g.fiber (IsLocalRing.closedPoint R)
  obtain ⟨p', hp'⟩ := mem_range_fiberι_of_eq (g := g) _ p hp
  let C : Set ↑F := irreducibleComponent p'
  have hC : IsIrreducible C := isIrreducible_irreducibleComponent
  have hCcl : IsClosed C := isClosed_irreducibleComponent
  let c : ↑F := hC.genericPoint
  have hc : IsGenericPoint c C := hC.isGenericPoint_genericPoint hCcl
  refine ⟨(g.fiberι _).base c, base_fiberι _ _, ?_⟩
  intro y hy hgy
  obtain ⟨y', rfl⟩ := mem_range_fiberι_of_eq (g := g) _ y hgy
  replace hy : y' ⤳ c := (specializes_fiberι_iff (g := g)
    (show Spec (CommRingCat.of R) from IsLocalRing.closedPoint R) y' c).mp hy
  have h1 : C ⊆ closure {y'} := by
    rw [← hc.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hy))
      isClosed_closure
  have h2 : closure {y'} = C := eq_irreducibleComponent
    isIrreducible_singleton.closure.isPreirreducible h1
  have hy' : IsGenericPoint y' C := by rw [← h2]; exact isGenericPoint_closure
  congr 1
  exact hy'.eq hc

theorem main (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ Z : B.Opens, (∃ z : B, z ∈ Z ∧ g.base z = IsLocalRing.closedPoint R) ∧
      ∀ z : B, z ∈ Z → g.base z = IsLocalRing.closedPoint R →
      ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
        [Module.Finite R R']
        (γ : Spec (CommRingCat.of R') ⟶ B) (hγ : γ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R
          R'))),
        γ.base (IsLocalRing.closedPoint R') = z →
      ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B)
        (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
        (hx : x ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        x.base (IsLocalRing.closedPoint K) ∈ S →
        (LB.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
            (schemeHomOverComp t rfl (⟨γ, hγ⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap R R'))) g))
            ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U := by
  classical
  choose sp hsp₁ hsp₂ using (exists_specializes_closedInFibre (g := g))
  let Zc : Set B := ⋃ s ∈ (S : Set B), closure (badSet LB U (sp s))
  have hZc : IsClosed Zc := S.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure
  refine ⟨⟨Zcᶜ, hZc.isOpen_compl⟩, ?_, ?_⟩
  · obtain ⟨η, hηk, hηmax⟩ := exists_maximal_specialFibre LB
    refine ⟨η, ?_, hηk⟩
    change η ∈ Zcᶜ
    intro hη
    obtain ⟨s, hs, hηs⟩ := Set.mem_iUnion₂.mp hη
    exact not_mem_closure_badSet LB U hU (sp s) (hsp₂ s) η hηk hηmax hηs
  · intro z hz hzk R' _ _ _ _ _ γ hγ hγz K _ x t hx hxS
    replace hz : z ∈ Zcᶜ := hz
    by_contra hbad
    set s' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R R')) with hs'
    let γ' : SchemeHomOver s' g := ⟨γ, hγ⟩
    let τ : pullback g s' ⟶ B := leftMul LB s' γ'
    let κ₁ : Spec (CommRingCat.of K) ⟶ pullback g s' := pullback.lift x t hx
    have e1 : (LB.mul (t ≫ s') (schemeHomOverComp t rfl γ') ⟨x, hx⟩).1 = κ₁ ≫ τ := by
      rw [comp_leftMul LB s' γ' κ₁ (t ≫ s') (by rw [← Category.assoc, pullback.lift_snd])]
      congr 2
      · apply Subtype.ext
        simp only [GoodReductionJacobian.schemeHomOverComp_coe, κ₁, pullback.lift_snd_assoc]
      · apply Subtype.ext
        simp only [κ₁, pullback.lift_fst]
    set b₁ : ↑(pullback g s') := κ₁.base (IsLocalRing.closedPoint K) with hb₁
    have hτb₁ : τ.base b₁ ∉ (U : Set B) := by
      intro h; apply hbad
      rw [e1]
      exact h
    set s : B := x.base (IsLocalRing.closedPoint K) with hsdef
    have hp₁b₁ : (pullback.fst g s').base b₁ = s := by
      exact congrArg (fun a : Spec (CommRingCat.of K) ⟶ B =>
        a (show Spec (CommRingCat.of K) from IsLocalRing.closedPoint K))
        (pullback.lift_fst x t hx)
    obtain ⟨b₀, hb₁b₀, hb₀s⟩ : ∃ b₀ : ↑(pullback g s'), b₁ ⤳ b₀ ∧ (pullback.fst g s').base b₀ = sp s
      := by
      have hfin : IsFinite s' := by
        rw [hs', IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
        infer_instance
      have hcl : IsClosed ((pullback.fst g s').base '' closure {b₁}) :=
        (pullback.fst g s').isClosedMap _ isClosed_closure
      have hmem : sp s ∈ (pullback.fst g s').base '' closure {b₁} := by
        have h1 : closure {s} ⊆ (pullback.fst g s').base '' closure {b₁} :=
          closure_minimal (Set.singleton_subset_iff.mpr ⟨b₁, subset_closure rfl, hp₁b₁⟩) hcl
        exact h1 ((specializes_iff_mem_closure).mp (hsp₁ s))
      obtain ⟨b₀, hb₀, e⟩ := hmem
      exact ⟨b₀, specializes_iff_mem_closure.mpr hb₀, e⟩
    have hτb₀ : τ.base b₀ ∉ (U : Set B) := fun h =>
      hτb₁ ((hb₁b₀.map τ.continuous).mem_open U.isOpen h)
    let κ₀ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ pullback g s' :=
      (pullback g s').fromSpecResidueField b₀
    let x₀ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ B := κ₀ ≫ pullback.fst g s'
    let p₀ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) :=
      IsLocalRing.closedPoint ((pullback g s').residueField b₀)
    have hκ₀ : κ₀ p₀ = b₀ := Scheme.fromSpecResidueField_apply b₀ p₀
    have hx₀pt : x₀.base (IsLocalRing.closedPoint ((pullback g s').residueField b₀)) = sp s :=
      (congrArg (fun b => (pullback.fst g s') b) hκ₀).trans hb₀s
    obtain ⟨u, hu⟩ : ∃ u : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ Spec
      (B.residueField (sp s)),
        u ≫ B.fromSpecResidueField (sp s) = x₀ := by
      refine ⟨Spec.map (B.descResidueField (Scheme.stalkClosedPointTo x₀)) ≫
        Spec.map (B.residueFieldCongr hx₀pt.symm).hom, ?_⟩
      rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
      exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField _ B x₀
    let γ₀ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ B := κ₀ ≫ pullback.snd g s' ≫
      γ
    have hbase : κ₀ ≫ (pullback.snd g s' ≫ s') = u ≫ (B.fromSpecResidueField (sp s) ≫ g) := by
      rw [← Category.assoc u, hu]; simp only [x₀, Category.assoc, pullback.condition]
    have hγ₀ : γ₀ ≫ g = u ≫ (B.fromSpecResidueField (sp s) ≫ g) := by
      rw [← hbase]; simp only [γ₀, Category.assoc, hγ]
    let q₁ : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ pullback g
      (B.fromSpecResidueField (sp s) ≫ g) :=
      pullback.lift γ₀ u hγ₀
    have key : q₁ ≫ rightMul LB (B.fromSpecResidueField (sp s) ≫ g) ⟨B.fromSpecResidueField (sp s),
      rfl⟩ =
        κ₀ ≫ τ := by
      rw [comp_rightMul LB _ _ q₁ (κ₀ ≫ (pullback.snd g s' ≫ s'))
          (by rw [hbase]; simp only [q₁, pullback.lift_snd_assoc]),
        comp_leftMul LB s' γ' κ₀ (κ₀ ≫ (pullback.snd g s' ≫ s')) rfl]
      congr 2
      · apply Subtype.ext
        simp only [q₁, γ₀, γ', pullback.lift_fst]
      · apply Subtype.ext
        simp only [q₁, pullback.lift_snd_assoc, hu, x₀]
    have hq₁bad : (rightMul LB (B.fromSpecResidueField (sp s) ≫ g) ⟨B.fromSpecResidueField (sp s),
      rfl⟩).base
        (q₁.base (IsLocalRing.closedPoint _)) ∉ (U : Set B) := by
      have he := congrArg
        (fun a : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ B => a p₀) key
      have he' : (rightMul LB (B.fromSpecResidueField (sp s) ≫ g)
          ⟨B.fromSpecResidueField (sp s), rfl⟩) (q₁ p₀) = τ b₀ :=
        he.trans (congrArg τ hκ₀)
      intro hmem
      exact hτb₀ (he' ▸ hmem)
    have hD : γ.base ((pullback.snd g s').base b₀) ∈ badSet LB U (sp s) := by
      refine ⟨q₁.base (IsLocalRing.closedPoint _), hq₁bad, ?_⟩
      have hf := congrArg
        (fun a : Spec (CommRingCat.of ((pullback g s').residueField b₀)) ⟶ B => a p₀)
        (pullback.lift_fst γ₀ u hγ₀)
      exact hf.trans (congrArg (fun b => γ ((pullback.snd g s') b)) hκ₀)
    have hbz : γ.base ((pullback.snd g s').base b₀) ⤳ z := by
      rw [← hγz]; exact (IsLocalRing.specializes_closedPoint _).map γ.continuous
    have hzC : z ∈ closure (badSet LB U (sp s)) := hbz.mem_closed isClosed_closure (subset_closure
      hD)
    exact hz (Set.mem_iUnion₂.mpr ⟨s, hxS, hzC⟩)

end Main

end TranslationNeighborhoods

end AbelianVarieties.NOSProofs.QuotientTranslationNeighborhoods

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
universe u

theorem exists_opens_forall_mul_base_mem_of_forall_specializes_mem
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ Z : B.Opens, (∃ z : B, z ∈ Z ∧ g.base z = IsLocalRing.closedPoint R) ∧
      ∀ z : B, z ∈ Z → g.base z = IsLocalRing.closedPoint R →
      ∀ (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
        [Module.Finite R R']
        (γ : Spec (CommRingCat.of R') ⟶ B) (hγ : γ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R
          R'))),
        γ.base (IsLocalRing.closedPoint R') = z →
      ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B)
        (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
        (hx : x ≫ g = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))),
        x.base (IsLocalRing.closedPoint K) ∈ S →
        (LB.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
            (schemeHomOverComp t rfl (⟨γ, hγ⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap R R'))) g))
            ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U :=
  AbelianVarieties.NOSProofs.QuotientTranslationNeighborhoods.TranslationNeighborhoods.main LB U hU
    S

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.QuotientEtaleNeighborhoods

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

noncomputable section

namespace EtaleSpread
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {N : Scheme.{u}} {i : N ⟶ G} {S' : Scheme.{u}} {j' : S' ⟶ G}

/-- The product of the subgroup and the candidate slice over the base field. -/
abbrev P (f : G ⟶ Spec (CommRingCat.of k)) (i : N ⟶ G) (j' : S' ⟶ G) : Scheme.{u} :=
  pullback (i ≫ f) (j' ≫ f)

/-- The structure morphism of the product with the slice. -/
abbrev tP (f : G ⟶ Spec (CommRingCat.of k)) (i : N ⟶ G) (j' : S' ⟶ G) :
    P f i j' ⟶ Spec (CommRingCat.of k) :=
  pullback.snd (i ≫ f) (j' ≫ f) ≫ j' ≫ f

/-- The group action restricted to the chosen slice. -/
def act (L : RelativeGroupLaw k f) (i : N ⟶ G) (j' : S' ⟶ G) : P f i j' ⟶ G :=
  pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i

/-- The first projection, viewed as a relative point. -/
def fstPt (f : G ⟶ Spec (CommRingCat.of k)) (i : N ⟶ G) (j' : S' ⟶ G) : SchemeHomOver (tP f i j') (i
  ≫ f) :=
  ⟨pullback.fst (i ≫ f) (j' ≫ f), by rw [pullback.condition]⟩

/-- The constant relative point induced by a base-field point. -/
def constPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : Spec (CommRingCat.of k) ⟶ N)
    (hn : n ≫ i ≫ f = 𝟙 _) : SchemeHomOver t (i ≫ f) :=
  ⟨t ≫ n, by rw [Category.assoc, hn, Category.comp_id]⟩

/-- Translation on the subgroup factor of the product. -/
def transl (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G) (n : Spec (CommRingCat.of k) ⟶ N)
    (hn : n ≫ i ≫ f = 𝟙 _) : P f i j' ⟶ P f i j' :=
  pullback.lift (LN.mul (tP f i j') (constPt (tP f i j') n hn) (fstPt f i j')).1 (pullback.snd (i ≫
    f) (j' ≫ f))
    ((LN.mul (tP f i j') (constPt (tP f i j') n hn) (fstPt f i j')).2)

/-- Left translation on the ambient relative group scheme. -/
def ltrans (L : RelativeGroupLaw k f) (g : Spec (CommRingCat.of k) ⟶ G) (hg : g ≫ f = 𝟙 _) : G ⟶ G
  :=
  (L.mul f ⟨f ≫ g, by rw [Category.assoc, hg, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1

/-- The unit section of the projection to the slice. -/
def sec (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G) : S' ⟶ P f i j' :=
  pullback.lift ((j' ≫ f) ≫ (LN.one (𝟙 _)).1) (𝟙 S')
    (by rw [Category.assoc, (LN.one (𝟙 _)).2, Category.comp_id, Category.id_comp])

@[scoped simp] theorem transl_fst (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G) (n : Spec
  (CommRingCat.of k) ⟶ N)
    (hn : n ≫ i ≫ f = 𝟙 _) :
    transl LN j' n hn ≫ pullback.fst _ _ = (LN.mul (tP f i j') (constPt (tP f i j') n hn) (fstPt f i
      j')).1 :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem transl_snd (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G) (n : Spec
  (CommRingCat.of k) ⟶ N)
    (hn : n ≫ i ≫ f = 𝟙 _) : transl LN j' n hn ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

theorem transl_tP (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G) (n : Spec (CommRingCat.of k) ⟶ N)
    (hn : n ≫ i ≫ f = 𝟙 _) : transl LN j' n hn ≫ tP f i j' = tP f i j' := by
  rw [← Category.assoc, transl_snd]

theorem ltrans_over (L : RelativeGroupLaw k f) (g : Spec (CommRingCat.of k) ⟶ G) (hg : g ≫ f = 𝟙 _)
  :
    ltrans L g hg ≫ f = f :=
  (L.mul f _ _).2

@[scoped simp] theorem sec_fst (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G) :
    sec LN j' ≫ pullback.fst _ _ = (j' ≫ f) ≫ (LN.one (𝟙 _)).1 := pullback.lift_fst _ _ _

@[scoped simp] theorem sec_snd (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G) :
    sec LN j' ≫ pullback.snd _ _ = 𝟙 S' := pullback.lift_snd _ _ _

end EtaleSpread

end

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

noncomputable section

namespace EtaleSpread
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {N : Scheme.{u}} {i : N ⟶ G} {S' : Scheme.{u}} {j' : S' ⟶ G}

theorem map_comp_actionSource (i : N ⟶ G) (j' : S' ⟶ G) :
    pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ actionSource f
          i =
      tP f i j' := by
  change pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.snd (i ≫ f) f ≫ f = pullback.snd (i ≫ f) (j' ≫ f)
    ≫ j' ≫ f
  rw [← Category.assoc, pullback.lift_snd, Category.assoc]

theorem act_eq (L : RelativeGroupLaw k f) (i : N ⟶ G) (j' : S' ⟶ G) :
    act L i j' = (L.mul (tP f i j')
      ⟨pullback.fst _ _ ≫ i, by simp only [Category.assoc, pullback.condition]⟩
      ⟨pullback.snd _ _ ≫ j', Category.assoc _ _ _⟩).1 := by
  rw [act, action_def]
  have h := L.mul_natural (actionSource f i) (tP f i j')
    (pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _))
    (map_comp_actionSource i j') (L.actionFstPoint i) (L.actionSndPoint i)
  have h1 := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
  rw [h1]
  congr 2
  · apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, actionFstPoint_coe, ← Category.assoc,
      pullback.lift_fst, Category.comp_id]
  · apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, actionSndPoint_coe, pullback.lift_snd]

theorem act_over (L : RelativeGroupLaw k f) (i : N ⟶ G) (j' : S' ⟶ G) : act L i j' ≫ f = tP f i j'
  := by
  rw [act_eq]; exact (L.mul _ _ _).2

theorem transl_comp_act (L : RelativeGroupLaw k f) (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G)
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _) :
    transl LN j' n hn ≫ act L i j' = act L i j' ≫ ltrans L (n ≫ i) ((Category.assoc n i f).trans hn)
      := by
  have lhs : transl LN j' n hn ≫ act L i j' =
      (L.mul (tP f i j') ⟨(LN.mul (tP f i j') (constPt (tP f i j') n hn) (fstPt f i j')).1 ≫ i, by
          rw [Category.assoc, (LN.mul _ _ _).2]⟩
        ⟨pullback.snd _ _ ≫ j', Category.assoc _ _ _⟩).1 := by
    rw [act_eq]
    have h := L.mul_natural (tP f i j') (tP f i j') (transl LN j' n hn) (transl_tP LN j' n hn)
      ⟨pullback.fst _ _ ≫ i, by simp only [Category.assoc, pullback.condition]⟩
      ⟨pullback.snd _ _ ≫ j', Category.assoc _ _ _⟩
    have h1 := congrArg Subtype.val h
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
    rw [h1]
    congr 2
    · apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, transl_fst]
    · apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, transl_snd]
  have hpush : (⟨(LN.mul (tP f i j') (constPt (tP f i j') n hn) (fstPt f i j')).1 ≫ i, by
          rw [Category.assoc, (LN.mul _ _ _).2]⟩ : SchemeHomOver (tP f i j') f) =
      L.mul (tP f i j') ⟨(tP f i j' ≫ n) ≫ i, by simp only [Category.assoc, hn, Category.comp_id]⟩
        ⟨pullback.fst _ _ ≫ i, by simp only [Category.assoc, pullback.condition]⟩ := by
    have h := hi (tP f i j') (constPt (tP f i j') n hn) (fstPt f i j')
    have h1 := congrArg Subtype.val h
    apply Subtype.ext
    exact h1
  have rhs : act L i j' ≫ ltrans L (n ≫ i) ((Category.assoc n i f).trans hn) =
      (L.mul (tP f i j') ⟨tP f i j' ≫ n ≫ i, by simp only [Category.assoc, hn, Category.comp_id]⟩
        ⟨act L i j', act_over L i j'⟩).1 := by
    rw [ltrans]
    have h := L.mul_natural f (tP f i j') (act L i j') (act_over L i j')
      ⟨f ≫ n ≫ i, by simp only [Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩
    have h1 := congrArg Subtype.val h
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
    rw [h1]
    congr 2
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, act_over]
  rw [lhs, rhs, hpush]
  have hact : (⟨act L i j', act_over L i j'⟩ : SchemeHomOver (tP f i j') f) =
      L.mul (tP f i j') ⟨pullback.fst _ _ ≫ i, by simp only [Category.assoc, pullback.condition]⟩
        ⟨pullback.snd _ _ ≫ j', Category.assoc _ _ _⟩ := by
    apply Subtype.ext; exact act_eq L i j'
  rw [hact, L.mul_assoc]
  rfl

end EtaleSpread

namespace EtaleSpread
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {N : Scheme.{u}} {i : N ⟶ G} {S' : Scheme.{u}} {j' : S' ⟶ G}

theorem constPt_eq_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : Spec (CommRingCat.of
  k) ⟶ N)
    (hn : n ≫ i ≫ f = 𝟙 _) :
    constPt t n hn = GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) (⟨n, hn⟩ :
      SchemeHomOver (𝟙 _) (i ≫ f)) := rfl

theorem comp_transl_eq_lift (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G)
    (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _)
    (ζ : Spec (CommRingCat.of k) ⟶ P f i j') (hζ : ζ ≫ tP f i j' = 𝟙 _)
    (h1 : LN.mul (𝟙 _) ⟨n, hn⟩ ⟨ζ ≫ pullback.fst _ _, by
        rw [Category.assoc, pullback.condition]; exact hζ⟩ = LN.one (𝟙 _)) :
    ζ ≫ transl LN j' n hn = pullback.lift (LN.one (𝟙 _)).1 (ζ ≫ pullback.snd _ _)
      (by rw [(LN.one _).2, Category.assoc]; exact hζ.symm) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, transl_fst]
    have h := LN.mul_natural (tP f i j') (𝟙 _) ζ hζ (constPt (tP f i j') n hn) (fstPt f i j')
    have h2 := congrArg Subtype.val h
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
    rw [h2, ← h1]
    congr 2
    · apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe]
      change ζ ≫ tP f i j' ≫ n = n
      rw [← Category.assoc, hζ, Category.id_comp]
  · rw [pullback.lift_snd, Category.assoc, transl_snd]

theorem transl_comp_transl (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G)
    (n₁ : Spec (CommRingCat.of k) ⟶ N) (hn₁ : n₁ ≫ i ≫ f = 𝟙 _)
    (n₂ : Spec (CommRingCat.of k) ⟶ N) (hn₂ : n₂ ≫ i ≫ f = 𝟙 _) :
    transl LN j' n₁ hn₁ ≫ transl LN j' n₂ hn₂ =
      transl LN j' (LN.mul (𝟙 _) ⟨n₂, hn₂⟩ ⟨n₁, hn₁⟩).1 (LN.mul (𝟙 _) ⟨n₂, hn₂⟩ ⟨n₁, hn₁⟩).2 := by
  apply pullback.hom_ext
  · rw [Category.assoc, transl_fst, transl_fst]
    have h := LN.mul_natural (tP f i j') (tP f i j') (transl LN j' n₁ hn₁) (transl_tP LN j' n₁ hn₁)
      (constPt (tP f i j') n₂ hn₂) (fstPt f i j')
    have h2 := congrArg Subtype.val h
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
    rw [h2]
    have e1 : GoodReductionJacobian.schemeHomOverComp (transl LN j' n₁ hn₁) (transl_tP LN j' n₁ hn₁)
      (constPt (tP f i j') n₂ hn₂) =
        constPt (tP f i j') n₂ hn₂ := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe]
      change transl LN j' n₁ hn₁ ≫ tP f i j' ≫ n₂ = tP f i j' ≫ n₂
      rw [← Category.assoc, transl_tP]
    have e2 : GoodReductionJacobian.schemeHomOverComp (transl LN j' n₁ hn₁) (transl_tP LN j' n₁ hn₁)
      (fstPt f i j') =
        LN.mul (tP f i j') (constPt (tP f i j') n₁ hn₁) (fstPt f i j') := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe]
      exact transl_fst LN j' n₁ hn₁
    rw [e1, e2, ← LN.mul_assoc]
    congr 2
    have h3 := LN.mul_natural (𝟙 _) (tP f i j') (tP f i j') (Category.comp_id _) ⟨n₂, hn₂⟩ ⟨n₁, hn₁⟩
    rw [constPt_eq_comp, constPt_eq_comp, ← h3]
    rfl
  · rw [Category.assoc, transl_snd, transl_snd, transl_snd]

theorem transl_one (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G) :
    transl LN j' (LN.one (𝟙 _)).1 (LN.one (𝟙 _)).2 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [transl_fst, Category.id_comp]
    have : constPt (tP f i j') (LN.one (𝟙 _)).1 (LN.one (𝟙 _)).2 = LN.one (tP f i j') := by
      rw [constPt_eq_comp]
      exact LN.one_natural (𝟙 _) (tP f i j') (tP f i j') (Category.comp_id _)
    rw [this, LN.one_mul]
    rfl
  · rw [transl_snd, Category.id_comp]

theorem isIso_transl (LN : RelativeGroupLaw k (i ≫ f)) (j' : S' ⟶ G)
    (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _) : IsIso (transl LN j' n hn) := by
  refine ⟨⟨transl LN j' (LN.inv (𝟙 _) ⟨n, hn⟩).1 (LN.inv (𝟙 _) ⟨n, hn⟩).2, ?_, ?_⟩⟩
  · rw [transl_comp_transl]
    have h : LN.mul (𝟙 _) ⟨(LN.inv (𝟙 _) ⟨n, hn⟩).1, (LN.inv (𝟙 _) ⟨n, hn⟩).2⟩ ⟨n, hn⟩ = LN.one (𝟙
      _) :=
      LN.inv_mul_cancel (𝟙 _) ⟨n, hn⟩
    have := transl_one LN j'
    revert this
    rw [← h]
    exact id
  · rw [transl_comp_transl]
    have h : LN.mul (𝟙 _) ⟨n, hn⟩ ⟨(LN.inv (𝟙 _) ⟨n, hn⟩).1, (LN.inv (𝟙 _) ⟨n, hn⟩).2⟩ = LN.one (𝟙
      _) :=
      LN.mul_inv_cancel (𝟙 _) ⟨n, hn⟩
    have := transl_one LN j'
    revert this
    rw [← h]
    exact id

theorem ltrans_comp_ltrans (L : RelativeGroupLaw k f) (g₁ : Spec (CommRingCat.of k) ⟶ G) (hg₁ : g₁ ≫
  f = 𝟙 _)
    (g₂ : Spec (CommRingCat.of k) ⟶ G) (hg₂ : g₂ ≫ f = 𝟙 _) :
    ltrans L g₁ hg₁ ≫ ltrans L g₂ hg₂ = ltrans L (L.mul (𝟙 _) ⟨g₂, hg₂⟩ ⟨g₁, hg₁⟩).1 (L.mul (𝟙 _)
      ⟨g₂, hg₂⟩ ⟨g₁, hg₁⟩).2 := by
  change ltrans L g₁ hg₁ ≫ (L.mul f ⟨f ≫ g₂, by rw [Category.assoc, hg₂, Category.comp_id]⟩ ⟨𝟙 G,
    Category.id_comp _⟩).1 =
    (L.mul f ⟨f ≫ (L.mul (𝟙 _) ⟨g₂, hg₂⟩ ⟨g₁, hg₁⟩).1, by rw [Category.assoc, (L.mul _ _ _).2,
      Category.comp_id]⟩
      ⟨𝟙 G, Category.id_comp _⟩).1
  have h := L.mul_natural f f (ltrans L g₁ hg₁) (ltrans_over L g₁ hg₁)
    ⟨f ≫ g₂, by rw [Category.assoc, hg₂, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩
  have h2 := congrArg Subtype.val h
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
  rw [h2]
  have e1 : GoodReductionJacobian.schemeHomOverComp (ltrans L g₁ hg₁) (ltrans_over L g₁ hg₁)
      (⟨f ≫ g₂, by rw [Category.assoc, hg₂, Category.comp_id]⟩ : SchemeHomOver f f) =
      ⟨f ≫ g₂, by rw [Category.assoc, hg₂, Category.comp_id]⟩ := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, ltrans_over]
  have e2 : GoodReductionJacobian.schemeHomOverComp (ltrans L g₁ hg₁) (ltrans_over L g₁ hg₁)
      (⟨𝟙 G, Category.id_comp _⟩ : SchemeHomOver f f) =
      L.mul f ⟨f ≫ g₁, by rw [Category.assoc, hg₁, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩ :=
        by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.comp_id]
    rfl
  rw [e1, e2, ← L.mul_assoc]
  congr 2
  have h3 := L.mul_natural (𝟙 _) f f (Category.comp_id _) ⟨g₂, hg₂⟩ ⟨g₁, hg₁⟩
  apply Subtype.ext
  exact (congrArg Subtype.val h3).symm

theorem ltrans_one (L : RelativeGroupLaw k f) : ltrans L (L.one (𝟙 _)).1 (L.one (𝟙 _)).2 = 𝟙 G := by
  rw [ltrans]
  have : (⟨f ≫ (L.one (𝟙 _)).1, by rw [Category.assoc, (L.one _).2, Category.comp_id]⟩ :
    SchemeHomOver f f) = L.one f := by
    have := L.one_natural (𝟙 _) f f (Category.comp_id _)
    rw [← this]
    rfl
  rw [this, L.one_mul]

theorem isIso_ltrans (L : RelativeGroupLaw k f) (g : Spec (CommRingCat.of k) ⟶ G) (hg : g ≫ f = 𝟙 _)
  :
    IsIso (ltrans L g hg) := by
  refine ⟨⟨ltrans L (L.inv (𝟙 _) ⟨g, hg⟩).1 (L.inv (𝟙 _) ⟨g, hg⟩).2, ?_, ?_⟩⟩
  · rw [ltrans_comp_ltrans]
    have h : L.mul (𝟙 _) ⟨(L.inv (𝟙 _) ⟨g, hg⟩).1, (L.inv (𝟙 _) ⟨g, hg⟩).2⟩ ⟨g, hg⟩ = L.one (𝟙 _) :=
      L.inv_mul_cancel (𝟙 _) ⟨g, hg⟩
    have := ltrans_one L
    revert this
    rw [← h]
    exact id
  · rw [ltrans_comp_ltrans]
    have h : L.mul (𝟙 _) ⟨g, hg⟩ ⟨(L.inv (𝟙 _) ⟨g, hg⟩).1, (L.inv (𝟙 _) ⟨g, hg⟩).2⟩ = L.one (𝟙 _) :=
      L.mul_inv_cancel (𝟙 _) ⟨g, hg⟩
    have := ltrans_one L
    revert this
    rw [← h]
    exact id

end EtaleSpread

end

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

noncomputable section

namespace EtaleSpread
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {N : Scheme.{u}} {i : N ⟶ G} {S' : Scheme.{u}}

theorem main [IsAlgClosed k] (f : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (L :
  RelativeGroupLaw k f)
    (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (j' : S' ⟶ G) [LocallyOfFiniteType (j' ≫ f)]
    (eS : Spec (CommRingCat.of k) ⟶ S') (heS : eS ≫ j' ≫ f = 𝟙 _)
    (W : (P f i j').Opens)
    (hzW : pullback.lift (LN.one (𝟙 _)).1 eS ((LN.one (𝟙 _)).2.trans heS.symm)
      (IsLocalRing.closedPoint k) ∈ W)
    (hW : Etale (W.ι ≫ act L i j')) :
    ∃ S₀ : S'.Opens, eS (IsLocalRing.closedPoint k) ∈ S₀ ∧
      Etale ((pullback.snd (i ≫ f) (j' ≫ f) ⁻¹ᵁ S₀).ι ≫ act L i j') := by
  let KP := {n : Spec (CommRingCat.of k) ⟶ N // n ≫ i ≫ f = 𝟙 _}
  let piece : KP → (P f i j').Opens := fun n => (transl LN j' n.1 n.2) ⁻¹ᵁ W
  have hpiece : ∀ n : KP, Etale ((piece n).ι ≫ act L i j') := by
    intro n
    have : IsIso (transl LN j' n.1 n.2) := isIso_transl LN j' n.1 n.2
    have hn' : (n.1 ≫ i) ≫ f = 𝟙 _ := by rw [Category.assoc]; exact n.2
    have : IsIso (ltrans L (n.1 ≫ i) hn') := isIso_ltrans L (n.1 ≫ i) hn'
    have hTa := transl_comp_act L LN j' hi n.1 n.2
    have ha : act L i j' = transl LN j' n.1 n.2 ≫ act L i j' ≫ CategoryTheory.inv (ltrans L (n.1 ≫
      i) hn') := by
      rw [← Category.assoc, hTa, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have e1 : (piece n).ι ≫ act L i j' =
        ((transl LN j' n.1 n.2) ∣_ W) ≫ (W.ι ≫ act L i j') ≫ CategoryTheory.inv (ltrans L (n.1 ≫ i)
          hn') := by
      change ((transl LN j' n.1 n.2) ⁻¹ᵁ W).ι ≫ act L i j' = _
      conv_lhs => rw [ha]
      rw [← Category.assoc, ← morphismRestrict_ι]
      simp only [Category.assoc]
    rw [e1]
    infer_instance
  let V : (P f i j').Opens := ⨆ n : KP, piece n
  have hV : Etale (V.ι ≫ act L i j') := by
    have localAtSource (P : MorphismProperty Scheme.{u})
        (Q : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop)
        [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance
    have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
      localAtSource _ RingHom.Etale
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) (fun n : KP => V.ι ⁻¹ᵁ piece n)
      (by rw [← Scheme.Hom.preimage_iSup]; exact V.ι_preimage_self)]
    intro n
    rw [← Category.assoc, ← Scheme.Opens.isoOfLE_hom_ι (le_iSup piece n), Category.assoc]
    infer_instance
  let S₀ : S'.Opens := (sec LN j') ⁻¹ᵁ W
  have hsec : eS ≫ sec LN j' = pullback.lift (LN.one (𝟙 _)).1 eS ((LN.one (𝟙 _)).2.trans heS.symm)
    := by
    apply pullback.hom_ext
    · rw [Category.assoc, sec_fst, pullback.lift_fst, ← Category.assoc, heS, Category.id_comp]
    · rw [Category.assoc, sec_snd, pullback.lift_snd, Category.comp_id]
  refine ⟨S₀, ?_, ?_⟩
  · have he := congrArg (fun a : Spec (CommRingCat.of k) ⟶ P f i j' =>
        a (show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k)) hsec
    have hw : (eS ≫ sec LN j')
        (show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k) ∈ W := he.symm ▸ hzW
    exact hw
  have hle : pullback.snd (i ≫ f) (j' ≫ f) ⁻¹ᵁ S₀ ≤ V := by
    have : JacobsonSpace (P f i j') := LocallyOfFiniteType.jacobsonSpace (tP f i j')
    intro z hz
    by_contra hzV
    obtain ⟨z₀, ⟨hz₀, hz₀V⟩, hz₀c⟩ := nonempty_inter_closedPoints (X := P f i j')
      (Z := ((pullback.snd (i ≫ f) (j' ≫ f) ⁻¹ᵁ S₀ : (P f i j').Opens) : Set (P f i j')) ∩ (V : Set
        (P f i j'))ᶜ)
      ⟨z, hz, hzV⟩ ((pullback.snd (i ≫ f) (j' ≫ f) ⁻¹ᵁ S₀).2.isLocallyClosed.inter
        V.2.isClosed_compl.isLocallyClosed)
    apply hz₀V
    let ζ := pointOfClosedPoint (tP f i j') z₀ hz₀c
    have hζ : ζ ≫ tP f i j' = 𝟙 _ := pointOfClosedPoint_comp _ _ _
    have hm : (ζ ≫ pullback.fst _ _) ≫ i ≫ f = 𝟙 _ := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]; exact hζ
    let mPt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f) := ⟨ζ ≫ pullback.fst _ _, hm⟩
    let nPt := LN.inv (𝟙 _) mPt
    have hn : nPt.1 ≫ i ≫ f = 𝟙 _ := nPt.2
    have h1 : LN.mul (𝟙 _) nPt mPt = LN.one (𝟙 _) := LN.inv_mul_cancel _ _
    have hT := comp_transl_eq_lift LN j' nPt.1 hn ζ hζ h1
    change z₀ ∈ ((⨆ n : KP, piece n : (P f i j').Opens) : Set (P f i j'))
    refine SetLike.mem_coe.mpr (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨nPt.1, hn⟩, ?_⟩)
    change (transl LN j' nPt.1 hn) z₀ ∈ W
    have hsec' : ζ ≫ pullback.snd _ _ ≫ sec LN j' = ζ ≫ transl LN j' nPt.1 hn := by
      rw [hT]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, sec_fst, pullback.lift_fst, ← Category.assoc, ←
        Category.assoc,
          show (ζ ≫ pullback.snd (i ≫ f) (j' ≫ f)) ≫ j' ≫ f = 𝟙 _ from hζ, Category.id_comp]
      · rw [Category.assoc, Category.assoc, sec_snd, pullback.lift_snd, Category.comp_id]
    have : (transl LN j' nPt.1 hn) z₀ = (sec LN j') ((pullback.snd (i ≫ f) (j' ≫ f)) z₀) := by
      let p : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
      have hζpt : ζ p = z₀ := pointOfClosedPoint_apply (tP f i j') z₀ hz₀c p
      have he := congrArg (fun a : Spec (CommRingCat.of k) ⟶ P f i j' => a p) hsec'
      exact (congrArg (transl LN j' nPt.1 hn) hζpt.symm).trans
        (he.symm.trans (congrArg (fun z => (sec LN j')
          ((pullback.snd (i ≫ f) (j' ≫ f)) z)) hζpt))
    rw [this]
    exact hz₀
  rw [← Scheme.homOfLE_ι _ hle, Category.assoc]
  infer_instance

end EtaleSpread

end

end AbelianVarieties.NOSProofs.QuotientEtaleNeighborhoods

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
universe u

theorem exists_opens_etale_preimage_snd_action_of_etale_nhds
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S' : Scheme.{u}) (j' : S' ⟶ G) [LocallyOfFiniteType (j' ≫ f)]
    (eS : Spec (CommRingCat.of k) ⟶ S') (heS : eS ≫ j' ≫ f = 𝟙 _)
    (W : (pullback (i ≫ f) (j' ≫ f)).Opens)
    (hzW : pullback.lift (LN.one (𝟙 _)).1 eS ((LN.one (𝟙 _)).2.trans heS.symm)
      (IsLocalRing.closedPoint k) ∈ W)
    (hW : Etale (W.ι ≫ (pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action
            i))) :
    ∃ S₀ : S'.Opens, eS (IsLocalRing.closedPoint k) ∈ S₀ ∧
      Etale ((pullback.snd (i ≫ f) (j' ≫ f) ⁻¹ᵁ S₀).ι ≫ (pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙
        N) j' (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
            :=
  AbelianVarieties.NOSProofs.QuotientEtaleNeighborhoods.EtaleSpread.main f L i LN hi j' eS heS W hzW
    hW

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_forall_mul_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.QuotientAffineNeighborhoods

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TranslateCoverAux

variable {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB :
  RelativeGroupLaw R g)

theorem mul_coe_congr {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (e : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ g) (P₂ Q₂ : SchemeHomOver t₂ g) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1)
      :
    (LB.mul t₁ P₁ Q₁).1 = (LB.mul t₂ P₂ Q₂).1 := by
  subst e
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

end TranslateCoverAux

end AbelianVarieties.NOSProofs.QuotientAffineNeighborhoods

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
universe u

open AbelianVarieties.NOSProofs.QuotientAffineNeighborhoods.TranslateCoverAux

theorem exists_isAffineOpen_forall_mem_of_forall_mul_mem
    {R : Type u} [CommRing R] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB :
      RelativeGroupLaw R g)
    {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of R))
    [IsFinite t₁] [Flat t₁] [LocallyOfFinitePresentation t₁] [Surjective t₁]
    (γ : SchemeHomOver t₁ g) (U : B.Opens) (hU : IsAffineOpen U) (S : Finset B)
    (hS : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ B) (t : Spec (CommRingCat.of K) ⟶
      T)
      (hx : x ≫ g = t ≫ t₁), x.base (IsLocalRing.closedPoint K) ∈ S →
      (LB.mul (t ≫ t₁) (schemeHomOverComp t rfl γ) ⟨x, hx⟩).1.base (IsLocalRing.closedPoint K) ∈ U)
        :
    ∃ V : B.Opens, IsAffineOpen V ∧ ∀ b ∈ S, b ∈ V := by
  classical
  let p : pullback g t₁ ⟶ B := pullback.fst g t₁
  let q : pullback g t₁ ⟶ T := pullback.snd g t₁
  have hpq : p ≫ g = q ≫ t₁ := pullback.condition
  let P₀ : SchemeHomOver (p ≫ g) g := ⟨p, rfl⟩
  let γq : SchemeHomOver (p ≫ g) g := schemeHomOverComp q hpq.symm γ
  let lam : pullback g t₁ ⟶ pullback g t₁ :=
    pullback.lift (LB.mul (p ≫ g) γq P₀).1 q (by rw [(LB.mul (p ≫ g) γq P₀).2, hpq])
  let lam' : pullback g t₁ ⟶ pullback g t₁ :=
    pullback.lift (LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀).1 q
      (by rw [(LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀).2, hpq])
  have lam_fst : lam ≫ p = (LB.mul (p ≫ g) γq P₀).1 := pullback.lift_fst _ _ _
  have lam_snd : lam ≫ q = q := pullback.lift_snd _ _ _
  have lam'_fst : lam' ≫ p = (LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀).1 := pullback.lift_fst _ _ _
  have lam'_snd : lam' ≫ q = q := pullback.lift_snd _ _ _
  have hlam : lam ≫ (p ≫ g) = p ≫ g := by rw [← Category.assoc, lam_fst, (LB.mul (p ≫ g) γq P₀).2]
  have hlam' : lam' ≫ (p ≫ g) = p ≫ g := by
    rw [← Category.assoc, lam'_fst, (LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀).2]
  have comp_γq : ∀ (μ : pullback g t₁ ⟶ pullback g t₁) (hμ : μ ≫ (p ≫ g) = p ≫ g) (hq : μ ≫ q = q),
      schemeHomOverComp μ hμ γq = γq := by
    intro μ hμ hq
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, γq, ← Category.assoc, hq]
  have h1 : lam ≫ lam' = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp]
      change lam ≫ lam' ≫ p = p
      rw [lam'_fst]
      have := congrArg Subtype.val
        (LB.mul_natural (p ≫ g) (p ≫ g) lam hlam (LB.inv (p ≫ g) γq) P₀)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, LB.inv_natural, comp_γq lam hlam lam_snd]
      have hP : schemeHomOverComp lam hlam P₀ = LB.mul (p ≫ g) γq P₀ := Subtype.ext lam_fst
      rw [hP, ← LB.mul_assoc, LB.inv_mul_cancel, LB.one_mul]
    · rw [Category.assoc, Category.id_comp]
      change lam ≫ lam' ≫ q = q
      rw [lam'_snd, lam_snd]
  have h2 : lam' ≫ lam = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.id_comp]
      change lam' ≫ lam ≫ p = p
      rw [lam_fst]
      have := congrArg Subtype.val (LB.mul_natural (p ≫ g) (p ≫ g) lam' hlam' γq P₀)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, comp_γq lam' hlam' lam'_snd]
      have hP : schemeHomOverComp lam' hlam' P₀ = LB.mul (p ≫ g) (LB.inv (p ≫ g) γq) P₀ :=
        Subtype.ext lam'_fst
      rw [hP, ← LB.mul_assoc, LB.mul_inv_cancel, LB.one_mul]
    · rw [Category.assoc, Category.id_comp]
      change lam' ≫ lam ≫ q = q
      rw [lam_snd, lam'_snd]
  have : IsIso lam := ⟨⟨lam', h1, h2⟩⟩
  let W : (pullback g t₁).Opens := lam ⁻¹ᵁ (p ⁻¹ᵁ U)
  have hW : IsAffineOpen W := (hU.preimage p).preimage lam
  have hSW : ∀ b₁ : ↥(pullback g t₁), p.base b₁ ∈ S → b₁ ∈ W := by
    intro b₁ hb₁
    change p.base (lam.base b₁) ∈ U
    let β := (pullback g t₁).fromSpecResidueField b₁
    have hx : (β ≫ p) ≫ g = (β ≫ q) ≫ t₁ := by rw [Category.assoc, hpq, Category.assoc]
    let pβ : Spec (CommRingCat.of ((pullback g t₁).residueField b₁)) :=
      IsLocalRing.closedPoint ((pullback g t₁).residueField b₁)
    have hβb : β pβ = b₁ := Scheme.fromSpecResidueField_apply b₁ pβ
    have hxS : (β ≫ p).base (IsLocalRing.closedPoint _) ∈ S :=
      (congrArg p hβb).symm ▸ hb₁
    have key := hS _ (β ≫ p) (β ≫ q) hx hxS
    have hβ : β ≫ (p ≫ g) = β ≫ p ≫ g := rfl
    have hnat := congrArg Subtype.val (LB.mul_natural (p ≫ g) (β ≫ p ≫ g) β hβ γq P₀)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at hnat
    have hcongr := mul_coe_congr LB (show β ≫ p ≫ g = (β ≫ q) ≫ t₁ by rw [hpq, Category.assoc])
      (schemeHomOverComp β hβ γq) (schemeHomOverComp β hβ P₀)
      (schemeHomOverComp (β ≫ q) rfl γ) ⟨β ≫ p, hx⟩
      (by simp only [GoodReductionJacobian.schemeHomOverComp_coe, γq, Category.assoc]) rfl
    have : p.base (lam.base b₁) = (β ≫ lam ≫ p).base (IsLocalRing.closedPoint _) :=
      congrArg (fun b => p (lam b)) hβb.symm
    rw [this, lam_fst, hnat, hcongr]
    exact key
  exact exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
    p S W hW hSW

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open AlgebraicGeometry.Smooth in
theorem exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens) (hU₁ : IsAffineOpen U)
    (hU₂ : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ V : B.Opens, IsAffineOpen V ∧ ∀ b ∈ S, b ∈ V := by
  classical
  obtain ⟨Z, ⟨z, hzZ, hz⟩, hZ⟩ :=
    exists_opens_forall_mul_base_mem_of_forall_specializes_mem
      LB U hU₂ S
  obtain ⟨R', _instCR, _instDom, _instDVR, _instAlg, _instFin, _instEt, _instFF, _instLoc,
    _instHens, a,
      _hmap, ha, haZ⟩ :=
    exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
      g Z z hz hzZ
  have hz' : g.base (a.base (IsLocalRing.closedPoint R')) = IsLocalRing.closedPoint R := by
    have h : g.base (a.base (IsLocalRing.closedPoint R')) =
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))).base (IsLocalRing.closedPoint R') := by
      exact congrArg (fun b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) =>
        b (show Spec (CommRingCat.of R') from IsLocalRing.closedPoint R')) ha
    rw [h]
    change PrimeSpectrum.comap (algebraMap R R') (IsLocalRing.closedPoint R') =
      IsLocalRing.closedPoint R
    exact IsLocalRing.comap_closedPoint (algebraMap R R')
  have hS := hZ (a.base (IsLocalRing.closedPoint R')) haZ hz' R' a ha rfl
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr ‹Module.Finite R R'›)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R')⟩
  exact GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_forall_mul_mem LB
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (⟨a, ha⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g) U hU₁ S hS

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (S : Finset B) :
    ∃ U : B.Opens, IsAffineOpen U ∧ ∀ b ∈ S, b ∈ U := by
  obtain ⟨U, hU₁, hU₂⟩ :=
    exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing g
  exact exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
    LB U hU₁ hU₂ S

end GoodReductionJacobian.RelativeGroupLaw
end

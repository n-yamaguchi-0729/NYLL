/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Tactic.Set
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.SchemeTheory.LocalGeometry.IntegralSmooth
public import Nyll.SchemeTheory.LocalGeometry.Normality
public import Nyll.AbelianVarieties.Geometry.PartialActions.Basic
public import Nyll.AbelianVarieties.Geometry.PartialActions.Maximality
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.Morphisms.AffineCompactification
public import Nyll.SchemeTheory.LocalGeometry.Dimension
public import Nyll.SchemeTheory.LocalGeometry.Points
public import Nyll.SchemeTheory.Morphisms.ValuativeProperness
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothOfRelativeDimensionLeTopologicalKrullDim
public import Nyll.SchemeTheory.Morphisms.SmoothRelativeDimension
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Stable boundary loci of partial group actions

Construct an invariant swept divisor with a rational point at which the identity acts.
Normalize a proper model and transport codimension-one boundary points to obtain a
compatible partial action with a stable boundary. Existing action calculus, normality,
and smooth integrality results provide the underlying structures.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace
open CategoryTheory.Limits hiding pair
open GoodReductionJacobian.PartialAction Topology
open SchemeTheory.ValuativeProperness.NormalCompactification
  (isIso_stalkMap_of_isIso_morphismRestrict)
open
  AbelianVarieties.NOSProofs.PartialActionTransport.GoodReductionJacobian.PartialAction.OpTransport
  (geometricallyIrreducible)
open
  AbelianVarieties.NOSProofs.PartialActionExistence.GoodReductionJacobian.PartialAction

universe u

/-- A point of an open subscheme with its membership witness. -/
def openPoint {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) :
    ↥(U : Scheme.{u}) :=
  ⟨x, hx⟩

private theorem openInclusion_apply {X : Scheme.{u}} (U : X.Opens)
    (z : ↥(U : Scheme.{u})) : U.ι z = z.1 := rfl

private theorem openPoint_ι {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) :
    U.ι (openPoint U x hx) = x := rfl

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_exists_stable_defined_one_of_closure_image_eq_closure_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.StableLocus

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open Topology

noncomputable section

namespace SweptDivisor

open
  AbelianVarieties.NOSProofs.PartialActionLaws.GoodReductionJacobian.PartialAction.ActionLaws
  (pair_comp defined_comp liftDom_eq act_comp comp_comp act_congr)
open
  AbelianVarieties.NOSProofs.PartialActionTransport.GoodReductionJacobian.PartialAction.OpTransport
  (geometricallyIrreducible)
open AbelianVarieties.NOSProofs.PartialActionTransport.GoodReductionJacobian.PartialAction
open _root_.GoodReductionJacobian.PartialAction
open _root_.GoodReductionJacobian

section General

variable {k : Type u} [Field k]

theorem dim_closure_add_one_le {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsIntegral P] [LocallyOfFiniteType p] (w' : P)
    (hw'₁ : ringKrullDim (P.presheaf.stalk w') = 1) :
    topologicalKrullDim ↥(closure ({w'} : Set P)) + 1 ≤ topologicalKrullDim P := by
  have h := AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral p w'
  rw [hw'₁, add_comm] at h
  exact h.le

theorem eq_of_closure_singleton_eq {X : Type u} [TopologicalSpace X] [T0Space X] {x y : X}
    (h : closure ({x} : Set X) = closure {y}) : x = y := by
  have h₁ : x ⤳ y := specializes_iff_mem_closure.mpr (h ▸ subset_closure rfl)
  have h₂ : y ⤳ x := specializes_iff_mem_closure.mpr (h.symm ▸ subset_closure rfl)
  exact (h₁.antisymm h₂).eq

end General

section Sweep

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}
  (a : PartialAction k f p)

/-- The set swept out by the closure of a point under the partial action. -/
def sweep (w : P) : Set P :=
  a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure {w})

theorem sweep_eq_image_closure {w : P} {ζ : ↥(pullback f p)} (hζ : ζ ∈ a.dom)
    (hcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w}) :
    sweep a w = a.hom.base '' closure {((openPoint a.dom ζ hζ) : ↥(a.dom : Scheme.{u}))} := by
  unfold sweep
  congr 1
  have himg : (a.dom.ι : ↥(a.dom : Scheme.{u}) → ↥(pullback f p)) '' {(openPoint a.dom ζ hζ)} =
    {ζ} := by
    exact Set.image_singleton
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← hcl,
    a.dom.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
  congr 2
  exact himg.symm

theorem hom_apply_eq_of_closure_sweep_eq {w w' : P} {ζ : ↥(pullback f p)} (hζ : ζ ∈ a.dom)
    (hcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w})
    (hsw : closure (sweep a w) = closure {w'}) :
    a.hom.base (openPoint a.dom ζ hζ) = w' := by
  rw [sweep_eq_image_closure a hζ hcl] at hsw
  apply eq_of_closure_singleton_eq
  rw [← hsw]
  apply le_antisymm
  · exact closure_mono (Set.singleton_subset_iff.2 ⟨_, subset_closure rfl, rfl⟩)
  · rw [← closure_closure (s := ({a.hom.base _} : Set P))]
    refine closure_mono ?_
    have h__af := (image_closure_subset_closure_image a.hom.base.hom.continuous
        (s := ({((openPoint a.dom ζ hζ) : ↥(a.dom : Scheme.{u}))} : Set _)))
    simp only [Set.image_singleton] at h__af
    exact h__af

theorem sweep_subset {w w' : P} (hsw : closure (sweep a w) = closure {w'}) :
    sweep a w ⊆ closure {w'} :=
  hsw ▸ subset_closure

end Sweep

section API

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} (a : PartialAction k f p)
  {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}

theorem act_apply {γ : SchemeHomOver t f} {x : SchemeHomOver t p} (hd : a.Defined γ x) (z : T)
    (d : ↥(a.dom : Scheme.{u})) (hdz : a.dom.ι d = pair γ x z) :
    (a.act γ x hd).1 z = a.hom d := by
  rw [act_coe, Scheme.Hom.comp_apply]
  congr 1
  apply a.dom.ι.injective
  rw [hdz, ← Scheme.Hom.comp_apply, liftDom_ι]

end API

section Incidence

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} (a : PartialAction k f p)

/-- The incidence scheme of a group element and a defined action. -/
abbrev R : Scheme.{u} := pullback (pullback.snd f p) a.hom

/-- The structure morphism of the incidence scheme. -/
abbrev tR : R a ⟶ Spec (CommRingCat.of k) :=
  pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p ≫ p

/-- The group coordinate of the second action. -/
def γR : SchemeHomOver (tR a) f :=
  ⟨pullback.fst (pullback.snd f p) a.hom ≫ pullback.fst f p, by
    simp only [tR, Category.assoc]
    rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, a.hom_comp]⟩

/-- The group coordinate of the initially defined action. -/
def δR : SchemeHomOver (tR a) f :=
  ⟨pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.fst f p, by
    simp only [tR, Category.assoc, pullback.condition]⟩

/-- The initial model coordinate in the incidence scheme. -/
def xR : SchemeHomOver (tR a) p :=
  ⟨pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p, by
    simp only [tR, Category.assoc]⟩

theorem pair_δR_xR : pair (δR a) (xR a) = pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; rfl
  · rw [pullback.lift_snd]; rfl

theorem defined_δR_xR : a.Defined (δR a) (xR a) := by
  unfold Defined
  rw [pair_δR_xR, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  refine (Set.image_subset_range _ _).trans ?_
  rw [Scheme.Opens.range_ι]

theorem liftDom_δR_xR : a.liftDom (δR a) (xR a) (defined_δR_xR a) =
    pullback.snd (pullback.snd f p) a.hom :=
  liftDom_eq a (δR a) (xR a) (defined_δR_xR a) _ (pair_δR_xR a).symm

theorem act_δR_xR_coe : (a.act (δR a) (xR a) (defined_δR_xR a)).1 =
    pullback.fst (pullback.snd f p) a.hom ≫ pullback.snd f p := by
  rw [act_coe, liftDom_δR_xR, pullback.condition]

theorem pair_γR_act : pair (γR a) (a.act (δR a) (xR a) (defined_δR_xR a)) =
    pullback.fst (pullback.snd f p) a.hom := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; rfl
  · rw [pullback.lift_snd, act_δR_xR_coe]

/-- The open incidence locus on which the second action is defined. -/
abbrev T₁ : (R a).Opens := pullback.fst (pullback.snd f p) a.hom ⁻¹ᵁ a.dom

/-- The structure morphism of the locus with two defined actions. -/
abbrev t₁ : (T₁ a : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := (T₁ a).ι ≫ tR a

/-- The second group coordinate restricted to the incidence open. -/
abbrev γ₁ : SchemeHomOver (t₁ a) f := GoodReductionJacobian.schemeHomOverComp (T₁ a).ι rfl (γR a)
/-- The first group coordinate restricted to the incidence open. -/
abbrev δ₁ : SchemeHomOver (t₁ a) f := GoodReductionJacobian.schemeHomOverComp (T₁ a).ι rfl (δR a)
/-- The model coordinate restricted to the incidence open. -/
abbrev x₁ : SchemeHomOver (t₁ a) p := GoodReductionJacobian.schemeHomOverComp (T₁ a).ι rfl (xR a)

theorem defined₁ : a.Defined (δ₁ a) (x₁ a) := defined_comp a _ _ _ _ (defined_δR_xR a)

theorem act₁_eq : a.act (δ₁ a) (x₁ a) (defined₁ a) =
    GoodReductionJacobian.schemeHomOverComp (T₁ a).ι rfl (a.act (δR a) (xR a) (defined_δR_xR a)) :=
  act_comp a _ _ _ _ _ _

theorem pair_γ₁_act₁ : pair (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) =
    (T₁ a).ι ≫ pullback.fst (pullback.snd f p) a.hom := by
  rw [act₁_eq, pair_comp, pair_γR_act]

theorem defined₂ : a.Defined (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) := by
  unfold Defined
  rw [pair_γ₁_act₁]
  rintro _ ⟨z, rfl⟩
  exact z.2

theorem assoc₁ (ha : a.Assoc L) :
    ∃ hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a),
      a.act (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) (defined₂ a) =
        a.act (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a) hd₃ :=
  ha (t₁ a) (γ₁ a) (δ₁ a) (x₁ a) (defined₁ a) (defined₂ a)

theorem hom_apply_mem_of_sweep_subset (ha : a.Assoc L) {w : P} {ζ ζ' : ↥(pullback f p)}
    (hζ : ζ ∈ a.dom) (hζw : pullback.snd f p ζ = w) (hζ' : ζ' ∈ a.dom)
    (hζ'w' : pullback.snd f p ζ' = a.hom ((openPoint a.dom ζ hζ) : ↥(a.dom : Scheme.{u})))
    {W : Set P} (hW : sweep a w ⊆ W) :
    a.hom.base ((openPoint a.dom ζ' hζ') : ↥(a.dom : Scheme.{u})) ∈ W := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f p)
    (g := a.hom) ζ' (openPoint a.dom ζ hζ) hζ'w'
  have hθT : θ ∈ T₁ a := by
    change pullback.fst (pullback.snd f p) a.hom θ ∈ a.dom
    rw [hθ₁]; exact hζ'
  obtain ⟨hd₃, heq⟩ := assoc₁ L a ha
  have hval := congrArg (fun s : SchemeHomOver (t₁ a) p => s.1 ((openPoint (T₁ a) θ hθT) : ↥((T₁
    a) : Scheme.{u}))) heq
  rw [act_apply a (defined₂ a) (openPoint (T₁ a) θ hθT)
    (openPoint a.dom ζ' hζ') (by
      rw [pair_γ₁_act₁]
      exact hθ₁.symm)] at hval
  rw [hval]
  set d := a.liftDom _ _ hd₃ ((openPoint (T₁ a) θ hθT) : ↥((T₁ a) : Scheme.{u})) with hd
  rw [act_coe, Scheme.Hom.comp_apply]
  apply hW
  refine ⟨d, ?_, rfl⟩
  change (a.dom.ι ≫ pullback.snd f p) d ∈ closure {w}
  have : (a.dom.ι ≫ pullback.snd f p) d = w := by
    rw [hd, ← Scheme.Hom.comp_apply, ← Category.assoc, liftDom_ι, pullback.lift_snd]
    change ((T₁ a).ι ≫ pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p) _ = w
    rw [Scheme.Hom.comp_apply, openPoint_ι, Scheme.Hom.comp_apply, hθ₂, ← hζw]
    rfl
  rw [this]
  exact subset_closure rfl

end Incidence

section GroupLaw

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)
  {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}

theorem inv_inv (x : SchemeHomOver t f) : L.inv t (L.inv t x) = x := by
  let : Group (SchemeHomOver t f) := L.pointGroup t
  exact _root_.inv_inv x

end GroupLaw

section Involution

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))

/-- The product containing two group coordinates and one model coordinate. -/
abbrev Q : Scheme.{u} := pullback f (pullback.snd f p ≫ p)

/-- The structure morphism of the triple product. -/
abbrev tQ : Q f p ⟶ Spec (CommRingCat.of k) :=
  pullback.snd f (pullback.snd f p ≫ p) ≫ pullback.snd f p ≫ p

/-- The first group coordinate of the triple product. -/
def γQ : SchemeHomOver (tQ f p) f :=
  ⟨pullback.fst f (pullback.snd f p ≫ p), by rw [pullback.condition]⟩

/-- The second group coordinate of the triple product. -/
def δQ : SchemeHomOver (tQ f p) f :=
  ⟨pullback.snd f (pullback.snd f p ≫ p) ≫ pullback.fst f p, by
    simp only [Category.assoc, pullback.condition]⟩

/-- The model coordinate of the triple product. -/
def xQ : SchemeHomOver (tQ f p) p :=
  ⟨pullback.snd f (pullback.snd f p ≫ p) ≫ pullback.snd f p, by simp only [Category.assoc]⟩

theorem pair_δQ_xQ : pair (δQ f p) (xQ f p) = pullback.snd f (pullback.snd f p ≫ p) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; rfl
  · rw [pullback.lift_snd]; rfl

/-- The involution sending the group pair to its inverse and product. -/
def ν : Q f p ⟶ Q f p :=
  pullback.lift (L.inv (tQ f p) (γQ f p)).1 (pair (L.mul (tQ f p) (γQ f p) (δQ f p)) (xQ f p)) (by
    rw [(L.inv (tQ f p) (γQ f p)).2, ← Category.assoc, pullback.lift_snd]
    exact (xQ f p).2.symm)

theorem ν_fst : ν f L p ≫ pullback.fst f _ = (L.inv (tQ f p) (γQ f p)).1 := pullback.lift_fst _ _ _

theorem ν_snd : ν f L p ≫ pullback.snd f _ = pair (L.mul (tQ f p) (γQ f p) (δQ f p)) (xQ f p) :=
  pullback.lift_snd _ _ _

theorem ν_snd_snd : ν f L p ≫ pullback.snd f _ ≫ pullback.snd f p =
    pullback.snd f _ ≫ pullback.snd f p := by
  rw [← Category.assoc, ν_snd, pullback.lift_snd]; rfl

theorem ν_tQ : ν f L p ≫ tQ f p = tQ f p := by
  have h := ν_snd_snd f L p
  calc ν f L p ≫ tQ f p
      = (ν f L p ≫ pullback.snd f _ ≫ pullback.snd f p) ≫ p := by simp only [tQ, Category.assoc]
    _ = (pullback.snd f _ ≫ pullback.snd f p) ≫ p := by rw [h]
    _ = tQ f p := by simp only [tQ, Category.assoc]

theorem comp_ν_γQ : GoodReductionJacobian.schemeHomOverComp (ν f L p) (ν_tQ f L p) (γQ f p) =
    L.inv (tQ f p) (γQ f p) :=
  Subtype.ext (ν_fst f L p)

theorem comp_ν_δQ : GoodReductionJacobian.schemeHomOverComp (ν f L p) (ν_tQ f L p) (δQ f p) =
    L.mul (tQ f p) (γQ f p) (δQ f p) := by
  apply Subtype.ext
  change ν f L p ≫ pullback.snd f _ ≫ pullback.fst f p = (L.mul (tQ f p) (γQ f p) (δQ f p)).1
  rw [← Category.assoc, ν_snd, pullback.lift_fst]

theorem comp_ν_xQ : GoodReductionJacobian.schemeHomOverComp (ν f L p) (ν_tQ f L p) (xQ f p) =
    xQ f p := by
  apply Subtype.ext
  change ν f L p ≫ pullback.snd f _ ≫ pullback.snd f p = pullback.snd f _ ≫ pullback.snd f p
  rw [← Category.assoc, ν_snd, pullback.lift_snd]
  rfl

theorem ν_ν : ν f L p ≫ ν f L p = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ν_fst, Category.id_comp]
    have h1 := L.inv_natural _ _ (ν f L p) (ν_tQ f L p) (γQ f p)
    rw [comp_ν_γQ, inv_inv] at h1
    exact congrArg Subtype.val h1
  · rw [Category.assoc, ν_snd, Category.id_comp, ← pair_δQ_xQ]
    have hm := L.mul_natural _ _ (ν f L p) (ν_tQ f L p) (γQ f p) (δQ f p)
    rw [comp_ν_γQ, comp_ν_δQ, OpTransport.inv_mul_cancel_left] at hm
    rw [← pair_comp (ν f L p) (ν_tQ f L p), hm, comp_ν_xQ]

scoped instance : IsIso (ν f L p) := ⟨⟨ν f L p, ν_ν f L p, ν_ν f L p⟩⟩

theorem ν_apply_eq_of_closure_eq {Ξ : ↥(Q f p)} {Z : Set P}
    (hΞ : closure ({Ξ} : Set ↥(Q f p)) =
      (pullback.snd f (pullback.snd f p ≫ p) ≫ pullback.snd f p).base ⁻¹' Z) :
    ν f L p Ξ = Ξ := by
  have hS : ∀ z, ν f L p z ∈ closure ({Ξ} : Set ↥(Q f p)) ↔ z ∈ closure ({Ξ} : Set ↥(Q f p)) := by
    intro z
    rw [hΞ, Set.mem_preimage, Set.mem_preimage, ← Scheme.Hom.comp_apply, ν_snd_snd]
  have hinv : ∀ z, ν f L p (ν f L p z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, ν_ν]; rfl
  have himg : (ν f L p).base '' closure {Ξ} = closure {Ξ} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hS y).2 hy
    · intro hz
      have h1 : ν f L p (ν f L p z) ∈ closure ({Ξ} : Set ↥(Q f p)) := by rw [hinv]; exact hz
      exact ⟨ν f L p z, (hS _).1 h1, hinv z⟩
  apply eq_of_closure_singleton_eq
  calc closure {ν f L p Ξ}
      = (ν f L p).homeomorph '' closure {Ξ} := by
        rw [(ν f L p).homeomorph.image_closure, Set.image_singleton]; rfl
    _ = closure {Ξ} := himg

end Involution

section Transport

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  (a : PartialAction k f p)

/-- The open embedding from the incidence scheme into the triple product. -/
def j : R a ⟶ Q f p :=
  (pullbackLeftPullbackSndIso f p a.hom).hom ≫
    pullback.map f (a.hom ≫ p) f (pullback.snd f p ≫ p) (𝟙 G) a.dom.ι (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, a.hom_comp])

scoped instance : IsOpenImmersion (j f p a) := by
  unfold j; infer_instance

theorem j_fst : j f p a ≫ pullback.fst f _ = pullback.fst _ _ ≫ pullback.fst f p := by
  unfold j
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
    Category.comp_id]

theorem j_snd : j f p a ≫ pullback.snd f _ = pullback.snd _ _ ≫ a.dom.ι := by
  unfold j
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd]

theorem j_tQ : j f p a ≫ tQ f p = tR a := by
  change j f p a ≫ pullback.snd f _ ≫ pullback.snd f p ≫ p = _
  rw [← Category.assoc, j_snd, Category.assoc]

theorem range_j : Set.range (j f p a).base = (pullback.snd f (pullback.snd f p ≫ p)).base ⁻¹'
    a.dom := by
  unfold j
  rw [Scheme.Hom.comp_base, TopCat.coe_comp,
    (ConcreteCategory.bijective_of_isIso (pullbackLeftPullbackSndIso f p
      a.hom).hom.base).2.range_comp,
    Scheme.Pullback.range_map]
  simp only [Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.coe_id, Set.range_id,
    Set.preimage_univ, Scheme.Opens.range_ι, Set.univ_inter]

theorem comp_j_γQ : GoodReductionJacobian.schemeHomOverComp (j f p a) (j_tQ f p a) (γQ f p) = γR a
    :=
  Subtype.ext (j_fst f p a)

theorem comp_j_δQ : GoodReductionJacobian.schemeHomOverComp (j f p a) (j_tQ f p a) (δQ f p) = δR a
    := by
  apply Subtype.ext
  change j f p a ≫ pullback.snd f _ ≫ pullback.fst f p = pullback.snd _ _ ≫ a.dom.ι ≫ pullback.fst
    f p
  rw [← Category.assoc, j_snd, Category.assoc]

theorem comp_j_xQ : GoodReductionJacobian.schemeHomOverComp (j f p a) (j_tQ f p a) (xQ f p) = xR a
    := by
  apply Subtype.ext
  change j f p a ≫ pullback.snd f _ ≫ pullback.snd f p = pullback.snd _ _ ≫ a.dom.ι ≫ pullback.snd
    f p
  rw [← Category.assoc, j_snd, Category.assoc]

variable {hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)}

/-- The inverse group element paired with the composed action. -/
def Ψ (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) : (T₁ a : Scheme.{u}) ⟶ pullback f p :=
  pair (L.inv (t₁ a) (γ₁ a)) (a.act _ _ hd₃)

/-- The incidence morphism induced by applying the inverse group element. -/
def ω (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) : (T₁ a : Scheme.{u}) ⟶ R a :=
  pullback.lift (Ψ f L p a hd₃) (a.liftDom _ _ hd₃) (by rw [Ψ, pullback.lift_snd, act_coe])

theorem ω_fst (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) :
    ω f L p a hd₃ ≫ pullback.fst _ _ = Ψ f L p a hd₃ := pullback.lift_fst _ _ _

theorem ω_snd (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) :
    ω f L p a hd₃ ≫ pullback.snd _ _ = a.liftDom _ _ hd₃ := pullback.lift_snd _ _ _

theorem ι_j_tQ : ((T₁ a).ι ≫ j f p a) ≫ tQ f p = t₁ a := by
  rw [Category.assoc, j_tQ]

theorem ω_j (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a)) :
    ω f L p a hd₃ ≫ j f p a = ((T₁ a).ι ≫ j f p a) ≫ ν f L p := by
  have hγ : GoodReductionJacobian.schemeHomOverComp ((T₁ a).ι ≫ j f p a) (ι_j_tQ f p a) (γQ f p) =
      γ₁ a := by
    rw [← comp_comp (T₁ a).ι rfl (j f p a) (j_tQ f p a), comp_j_γQ]
  have hδ : GoodReductionJacobian.schemeHomOverComp ((T₁ a).ι ≫ j f p a) (ι_j_tQ f p a) (δQ f p) =
      δ₁ a := by
    rw [← comp_comp (T₁ a).ι rfl (j f p a) (j_tQ f p a), comp_j_δQ]
  have hx : GoodReductionJacobian.schemeHomOverComp ((T₁ a).ι ≫ j f p a) (ι_j_tQ f p a) (xQ f p) =
      x₁ a := by
    rw [← comp_comp (T₁ a).ι rfl (j f p a) (j_tQ f p a), comp_j_xQ]
  apply pullback.hom_ext
  · rw [Category.assoc, j_fst, ← Category.assoc, ω_fst, Ψ, pullback.lift_fst, Category.assoc, ν_fst]
    have h := L.inv_natural _ _ ((T₁ a).ι ≫ j f p a) (ι_j_tQ f p a) (γQ f p)
    rw [hγ] at h
    exact (congrArg Subtype.val h).symm
  · rw [Category.assoc, j_snd, ← Category.assoc, ω_snd, liftDom_ι, Category.assoc, ν_snd,
      ← pair_comp _ (ι_j_tQ f p a), L.mul_natural, hγ, hδ, hx]

end Transport

section Generic

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  (a : PartialAction k f p)

theorem eq_of_mem_closure_of_mem_closure {X : Type u} [TopologicalSpace X] [T0Space X] {x y : X}
    (h₁ : x ∈ closure ({y} : Set X)) (h₂ : y ∈ closure ({x} : Set X)) : x = y :=
  ((specializes_iff_mem_closure.mpr h₂).antisymm (specializes_iff_mem_closure.mpr h₁)).eq

theorem exists_mem_T₁_Ψ_eq [GeometricallyIrreducible f] [LocallyOfFiniteType f]
    [LocallyOfFiniteType p]
    (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a))
    {w : P} {ζ ζ' : ↥(pullback f p)} (hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure {w})
    (hζ' : ζ' ∈ a.dom)
    (hζ'cl : closure ({ζ'} : Set ↥(pullback f p)) =
      (pullback.snd f p).base ⁻¹' closure {a.hom ((openPoint a.dom ζ hζ) : ↥(a.dom : Scheme.{u}))})
    (hζ'snd : pullback.snd f p ζ' = a.hom ((openPoint a.dom ζ hζ) : ↥(a.dom : Scheme.{u}))) :
    ∃ (r : ↥(R a)) (hr : r ∈ T₁ a), Ψ f L p a hd₃ (openPoint (T₁ a) r hr) = ζ' ∧
      pullback.snd (pullback.snd f p) a.hom r = (openPoint a.dom ζ hζ) := by
  obtain ⟨Ξ, hΞcl, hΞζ, -⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f
      (pullback.snd f p ≫ p) ζ
  have hΞM : Ξ ∈ Set.range (j f p a).base := by
    rw [range_j]
    change pullback.snd f _ Ξ ∈ a.dom
    rw [hΞζ]; exact hζ
  obtain ⟨ΞR, hΞR⟩ := hΞM
  have hsndR : pullback.snd (pullback.snd f p) a.hom ΞR = (openPoint a.dom ζ hζ) := by
    apply a.dom.ι.injective
    rw [← Scheme.Hom.comp_apply, ← j_snd, Scheme.Hom.comp_apply, hΞR, hΞζ, openPoint_ι]
  have h1 : pullback.fst (pullback.snd f p) a.hom ΞR ∈ closure ({ζ'} : Set ↥(pullback f p)) := by
    rw [hζ'cl, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      hsndR]
    exact subset_closure rfl
  obtain ⟨θ, hθ₁, hθ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f p)
    (g := a.hom) ζ' (openPoint a.dom ζ hζ) hζ'snd
  have hθcl : θ ∈ closure ({ΞR} : Set ↥(R a)) := by
    rw [(j f p a).isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
      Set.mem_preimage]
    rw [hΞR, hΞcl, Set.mem_preimage, ← Scheme.Hom.comp_apply, j_snd, Scheme.Hom.comp_apply, hθ₂,
      openInclusion_apply]
    exact subset_closure rfl
  have h2 : ζ' ∈ closure ({pullback.fst (pullback.snd f p) a.hom ΞR} : Set ↥(pullback f p)) := by
    have := image_closure_subset_closure_image
      (pullback.fst (pullback.snd f p) a.hom).base.hom.continuous ⟨θ, hθcl, rfl⟩
    rwa [Set.image_singleton, hθ₁] at this
  have hfst : pullback.fst (pullback.snd f p) a.hom ΞR = ζ' := eq_of_mem_closure_of_mem_closure h1
    h2
  have hT : ΞR ∈ T₁ a := by
    change pullback.fst (pullback.snd f p) a.hom ΞR ∈ a.dom
    rw [hfst]; exact hζ'
  have e1 : Ψ f L p a hd₃ (openPoint (T₁ a) ΞR hT) =
      pullback.fst (pullback.snd f p) a.hom (ω f L p a hd₃ (openPoint (T₁ a) ΞR hT)) := by
    rw [← Scheme.Hom.comp_apply, ω_fst]
  have e2 : j f p a (ω f L p a hd₃ (openPoint (T₁ a) ΞR hT)) = j f p a ΞR := by
    rw [← Scheme.Hom.comp_apply, ω_j, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      openInclusion_apply]
    change ν f L p (j f p a ΞR) = j f p a ΞR
    rw [hΞR]
    exact ν_apply_eq_of_closure_eq f L p (Z := closure {w}) (by
      rw [hΞcl, hζcl, ← Set.preimage_comp]; rfl)
  have e3 : ω f L p a hd₃ (openPoint (T₁ a) ΞR hT) = ΞR := (j f p a).injective e2
  exact ⟨ΞR, hT, by rw [e1, e3, hfst], hsndR⟩

end Generic

section Final

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
  (a : PartialAction k f p)

theorem stable_of_closure_eq {W : Set P} (hWc : IsClosed W) {ζ' : ↥(pullback f p)} (hζ' : ζ' ∈
    a.dom)
    (hcl : closure ({ζ'} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' W)
    (hmem : a.hom ((openPoint a.dom ζ' hζ') : ↥(a.dom : Scheme.{u})) ∈ W) : a.Stable W := by
  intro z hz
  have hz' : z ∈ closure ({(openPoint a.dom ζ' hζ')} : Set ↥(a.dom : Scheme.{u})) := by
    rw [a.dom.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
      Set.mem_preimage, openPoint_ι, hcl]
    exact hz
  have h := image_closure_subset_closure_image a.hom.base.hom.continuous ⟨z, hz', rfl⟩
  rw [Set.image_singleton] at h
  exact closure_minimal (Set.singleton_subset_iff.2 hmem) hWc h

theorem exists_rational_defined_one [IsAlgClosed k] [LocallyOfFiniteType (tR a)] (ha : a.Assoc L)
    (hd₃ : a.Defined (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a))
    (heq : a.act (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) (defined₂ a) =
      a.act (L.mul (t₁ a) (γ₁ a) (δ₁ a)) (x₁ a) hd₃)
    {r : ↥(R a)} (hr : r ∈ T₁ a) (hΨr : Ψ f L p a hd₃ (openPoint (T₁ a) r hr) ∈ a.dom) {w : P}
    (hrw : (pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p) r ∈ closure {w})
    {W : Set P} (hW : sweep a w ⊆ W) :
    ∃ P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
      P₀.1 (fieldPoint k) ∈ W ∧
      a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by
  let T₃ : (T₁ a : Scheme.{u}).Opens := Ψ f L p a hd₃ ⁻¹ᵁ a.dom
  let A : Set ↥(R a) := ((T₁ a).ι ''ᵁ T₃ : Set ↥(R a)) ∩
    (pullback.snd (pullback.snd f p) a.hom ≫ a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure {w}
  have hA : IsLocallyClosed A :=
    ((T₁ a).ι ''ᵁ T₃).isOpen.isLocallyClosed.inter
      (isClosed_closure.preimage (Scheme.Hom.continuous _)).isLocallyClosed
  have hAne : A.Nonempty := ⟨r, ⟨(openPoint (T₁ a) r hr), hΨr, rfl⟩, hrw⟩
  have : JacobsonSpace ↥(R a) := LocallyOfFiniteType.jacobsonSpace (tR a)
  obtain ⟨t, ⟨⟨t₁', ht₃, ht₁⟩, htw⟩, htc⟩ := nonempty_inter_closedPoints hAne hA
  obtain ⟨τ, hτ, hτt⟩ :=
    AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton (tR a) k
      t htc
  change τ (fieldPoint k) = t at hτt
  have hτ1 : τ ≫ tR a = 𝟙 _ := by
    rw [hτ, Algebra.algebraMap_self]
    exact Spec.map_id _
  have hτT : Set.range τ.base ⊆ Set.range (T₁ a).ι.base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = fieldPoint k := Subsingleton.elim _ _
    exact ⟨t₁', ht₁.trans hτt.symm⟩
  let τ₁ : Spec (CommRingCat.of k) ⟶ (T₁ a : Scheme.{u}) := IsOpenImmersion.lift (T₁ a).ι τ hτT
  have hτ₁ : τ₁ ≫ (T₁ a).ι = τ := IsOpenImmersion.lift_fac _ _ _
  have hτ₁t : τ₁ (fieldPoint k) = t₁' := by
    apply (T₁ a).ι.injective
    rw [← Scheme.Hom.comp_apply, hτ₁, hτt]
    exact ht₁.symm
  have hs : τ₁ ≫ t₁ a = 𝟙 _ := by
    change τ₁ ≫ (T₁ a).ι ≫ tR a = 𝟙 _
    rw [← Category.assoc, hτ₁, hτ1]
  have hd01 : a.Defined (GoodReductionJacobian.schemeHomOverComp τ₁ hs (δ₁ a))
      (GoodReductionJacobian.schemeHomOverComp τ₁ hs (x₁ a)) := defined_comp a τ₁ hs _ _ (defined₁
        a)
  have hy : a.act _ _ hd01 =
      GoodReductionJacobian.schemeHomOverComp τ₁ hs (a.act (δ₁ a) (x₁ a) (defined₁ a)) :=
    act_comp a τ₁ hs _ _ (defined₁ a) hd01
  have hd02' : a.Defined (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a))
      (GoodReductionJacobian.schemeHomOverComp τ₁ hs (a.act (δ₁ a) (x₁ a) (defined₁ a))) :=
    defined_comp a τ₁ hs _ _ (defined₂ a)
  have hd02 : a.Defined (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a)) (a.act _ _
    hd01) := by
    rw [hy]; exact hd02'
  have hact2 : a.act _ _ hd02 = GoodReductionJacobian.schemeHomOverComp τ₁ hs
      (a.act (γ₁ a) (a.act (δ₁ a) (x₁ a) (defined₁ a)) (defined₂ a)) := by
    rw [act_congr a rfl hy hd02 hd02']
    exact act_comp a τ₁ hs _ _ (defined₂ a) hd02'
  have hd0inv : a.Defined (L.inv _ (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a)))
      (a.act _ _ hd02) := by
    have hp : pair (L.inv _ (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a))) (a.act _ _
      hd02) =
        τ₁ ≫ Ψ f L p a hd₃ := by
      rw [hact2, heq, ← L.inv_natural _ _ τ₁ hs (γ₁ a), pair_comp]
      rfl
    unfold Defined
    rw [hp]
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = fieldPoint k := Subsingleton.elim _ _
    rw [Scheme.Hom.comp_apply, hτ₁t]
    exact ht₃
  obtain ⟨hd0e, -⟩ := ha _ (L.inv _ (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a)))
    (GoodReductionJacobian.schemeHomOverComp τ₁ hs (γ₁ a)) (a.act _ _ hd01) hd02 hd0inv
  rw [L.inv_mul_cancel] at hd0e
  refine ⟨a.act _ _ hd01, ?_, hd0e⟩
  rw [hy, GoodReductionJacobian.schemeHomOverComp_coe, act₁_eq,
    GoodReductionJacobian.schemeHomOverComp_coe, act_δR_xR_coe, ← Category.assoc, hτ₁,
    Scheme.Hom.comp_apply, hτt, pullback.condition, Scheme.Hom.comp_apply]
  apply hW
  refine ⟨_, ?_, rfl⟩
  rw [Set.mem_preimage, Scheme.Hom.comp_apply] at htw
  exact htw

end Final

end SweptDivisor

end

end AbelianVarieties.NOSProofs.StableLocus

namespace GoodReductionJacobian.PartialAction

open AbelianVarieties.NOSProofs.StableLocus.SweptDivisor

theorem
    exists_stable_defined_one_of_closure_image_eq_closure_singleton
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (a : PartialAction k f p) (_hu : a.UnitActs L) (ha : a.Assoc L)
    (hcod : ∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom)
    (w w' : P) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1)
    (hw'₁ : ringKrullDim (P.presheaf.stalk w') = 1)
    (hsw : closure (a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure {w})) =
      closure {w'}) :
    ∃ P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
      topologicalKrullDim ↥(closure {w'}) + 1 ≤ topologicalKrullDim ↥P ∧
      a.Stable (closure {w'}) ∧
      P₀.1 (IsLocalRing.closedPoint k) ∈ closure {w'} ∧
      a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by
  have : GeometricallyIrreducible f :=
    geometricallyIrreducible L
  obtain ⟨ζ, hζcl, hζw, hζdim⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f p w
  have hζ : ζ ∈ a.dom := hcod ζ (hζdim.trans hw₁).le
  have hWsub : sweep a w ⊆ closure {w'} := sweep_subset a hsw
  have hw'eq : a.hom.base ((openPoint a.dom ζ hζ) : ↥(a.dom : Scheme.{u})) = w' :=
    hom_apply_eq_of_closure_sweep_eq a hζ hζcl hsw
  obtain ⟨ζ', hζ'cl, hζ'w', hζ'dim⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f p w'
  have hζ' : ζ' ∈ a.dom := hcod ζ' (hζ'dim.trans hw'₁).le
  have hmem : a.hom ((openPoint a.dom ζ' hζ') : ↥(a.dom : Scheme.{u})) ∈ closure ({w'} : Set P) :=
    hom_apply_mem_of_sweep_subset L a ha hζ hζw hζ' (by rw [hζ'w', hw'eq]) hWsub
  have hstab : a.Stable (closure {w'}) := stable_of_closure_eq f p a isClosed_closure hζ' hζ'cl hmem
  obtain ⟨hd₃, heq⟩ := assoc₁ L a ha
  obtain ⟨r, hr, hΨ, hrsnd⟩ := exists_mem_T₁_Ψ_eq f L p a hd₃ hζ hζcl hζ'
    (by rw [hw'eq]; exact hζ'cl) (by rw [hw'eq]; exact hζ'w')
  obtain ⟨P₀, hP₀W, hP₀e⟩ := exists_rational_defined_one f L p a ha hd₃ heq hr
    (by rw [hΨ]; exact hζ') (w := w) (by
      rw [Scheme.Hom.comp_apply, hrsnd, Scheme.Hom.comp_apply, openPoint_ι, hζw]
      exact subset_closure rfl) hWsub
  exact ⟨P₀, dim_closure_add_one_le p w' hw'₁, hstab, hP₀W, hP₀e⟩

end GoodReductionJacobian.PartialAction
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.StableLocus

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace
open CategoryTheory.Limits hiding pair

namespace BoundaryModel

open SchemeTheory.ValuativeProperness.NormalCompactification
  (isIso_stalkMap_of_isIso_morphismRestrict)

theorem isProper_of_comp_eq {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY
    : Y ⟶ Spec (.of k))
    [IsProper fX] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = fX) : IsProper g := by
  have : IsProper (g ≫ fY) := by rw [hg]; infer_instance
  exact IsProper.of_comp g fY

theorem eq_genericPoint_of_ringKrullDim_stalk_eq_zero
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
      [IsIntegral X]
    (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 0) : x = genericPoint X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hh : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.height = 0 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      (X.presheaf.stalk x)
    rw [hx] at this
    exact_mod_cast this.symm
  have hmin : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal = ⊥ := by
    have h0 := Ideal.height_eq_zero_iff.mp hh
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at h0
    exact h0
  have hgen : hU.primeIdealOf ⟨x, hxU⟩ = genericPoint (Spec Γ(X, U)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hmin
  calc x = hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) := (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm
    _ = hU.fromSpec (genericPoint (Spec Γ(X, U))) := by rw [hgen]
    _ = genericPoint X :=
      @genericPoint_eq_of_isOpenImmersion (Spec Γ(X, U)) X hU.fromSpec
        hU.isOpenImmersion_fromSpec inferInstance inferInstance

theorem isIntegral_pullback_of_geometricallyIrreducible_of_smooth
    {k : Type u} [Field k] {G P : Scheme.{u}} (f : G ⟶ Spec (.of k)) (p : P ⟶ Spec (.of k))
    [GeometricallyIrreducible f] [Smooth f] [LocallyOfFiniteType p] [IsIntegral P] :
    IsIntegral (pullback f p) := by
  have : IrreducibleSpace ↥(pullback f p) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsReduced (pullback f p) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd f p)
  have : Nonempty ↥(pullback f p) := inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end BoundaryModel

namespace BoundaryModel

open SchemeTheory.ValuativeProperness.NormalCompactification
  (isIso_stalkMap_of_isIso_morphismRestrict)

theorem denseRange_hom_of_compatible
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f] (L :
      GoodReductionJacobian.RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι₀ : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι₀]
      (hι₀ : ι₀ ≫ p = V.ι ≫ f)
    (a : GoodReductionJacobian.PartialAction k f p) (hc : a.Compatible L V ι₀ hι₀) : DenseRange
      a.hom.base := by
  let t : (V : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := V.ι ≫ f
  let v : NeronModelInfra.SchemeHomOver t (V.ι ≫ f) := ⟨𝟙 _, Category.id_comp _⟩
  have hmul : NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : NeronModelInfra.SchemeHomOver (V.ι
    ≫ f) f) =
      L.mul t (L.one t) (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ :
        NeronModelInfra.SchemeHomOver (V.ι ≫ f) f)) :=
    (L.one_mul t _).symm
  obtain ⟨hd, hact⟩ := hc t (L.one t) v v hmul
  have hfac : a.liftDom (L.one t) (GoodReductionJacobian.PartialAction.modelPoint ι₀ hι₀ v) hd ≫
    a.hom = ι₀ := by
    have := congrArg Subtype.val hact
    simpa only [GoodReductionJacobian.PartialAction.act_coe,
      GoodReductionJacobian.PartialAction.modelPoint_coe, v, Category.id_comp] using this
  have hsub : Set.range ι₀.base ⊆ Set.range a.hom.base := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(a.liftDom (L.one t) (GoodReductionJacobian.PartialAction.modelPoint ι₀ hι₀ v) hd).base
      y, by
      rw [← Scheme.Hom.comp_apply, hfac]⟩
  have hdense : Dense (Set.range ι₀.base) :=
    ι₀.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  exact hdense.mono hsub

end BoundaryModel

end AbelianVarieties.NOSProofs.StableLocus

namespace GoodReductionJacobian.PartialAction

open AbelianVarieties.NOSProofs.StableLocus.BoundaryModel

theorem
    exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ G) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι)
    (w : P) (hw : w ∉ (D : Set P)) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1) :
    ∃ (P' : Scheme.{u}) (π : P' ⟶ P) (V' : G.Opens)
      (ι' : (V' : Scheme.{u}) ⟶ P') (hι' : ι' ≫ π ≫ p = V'.ι ≫ f) (a' : PartialAction k f (π ≫ p))
      (w' w'' : P'),
      IsIntegral P' ∧ (∀ y : P', IsIntegrallyClosed (P'.presheaf.stalk y)) ∧ IsProper π ∧
      topologicalKrullDim ↥P' = topologicalKrullDim ↥G ∧
      Nonempty (V' : Scheme.{u}) ∧ IsOpenImmersion ι' ∧
      a'.Compatible L V' ι' hι' ∧ a'.Maximal ∧
      (∀ z : ↥(pullback f (π ≫ p)),
        ringKrullDim ((pullback f (π ≫ p)).presheaf.stalk z) ≤ 1 → z ∈ a'.dom) ∧
      π.base w' = w ∧
      ringKrullDim (P'.presheaf.stalk w') = 1 ∧ ringKrullDim (P'.presheaf.stalk w'') = 1 ∧
      closure (a'.hom.base '' ((a'.dom.ι ≫ pullback.snd f (π ≫ p)).base ⁻¹' closure {w'})) =
        closure {w''} := by
  have hι₀ : (ι ≫ D.ι) ≫ p = V.ι ≫ f := by rw [Category.assoc, ← hτ, ← Category.assoc, hτι]
  have : IsOpenImmersion (ι ≫ D.ι) := inferInstance
  obtain ⟨a, hc, hm, hcod⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_partialAction_compatible_maximal_of_isProper k f
      L p hn V (ι ≫ D.ι) hι₀
  have : GeometricallyIrreducible f := geometricallyIrreducible L
  have : LocallyOfFiniteType f := inferInstance
  obtain ⟨ζ, hζcl, hζw, hζdim⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f p w
  have hζ₁ : ringKrullDim ((pullback f p).presheaf.stalk ζ) = 1 := by rw [hζdim, hw₁]
  have hζdom : ζ ∈ a.dom := hcod ζ (by rw [hζ₁])
  have : IsIntegral (pullback f p) :=
    isIntegral_pullback_of_geometricallyIrreducible_of_smooth f p
  have hζn : IsIntegrallyClosed ((pullback f p).presheaf.stalk ζ) :=
    InducedAction.isIntegrallyClosed_stalk (f := f) (p := p) hn ζ
  have : Nonempty ↥(a.dom : Scheme.{u}) := ⟨⟨ζ, hζdom⟩⟩
  have : IsIntegral (a.dom : Scheme.{u}) := inferInstance
  have : LocallyOfFiniteType p := inferInstance
  have hdomα : DenseRange a.hom.base := denseRange_hom_of_compatible k f L p V (ι ≫ D.ι) hι₀ a hc
  have hbd : a.hom.base ⟨ζ, hζdom⟩ ∉ (D : Set P) :=
    GoodReductionJacobian.PartialAction.hom_base_notMem_of_snd_notMem_of_isProper k f L p D τ hτ V
      ι hτι a hc ⟨ζ, hζdom⟩ (by
      change (pullback.snd f p).base ζ ∉ (D : Set P); rw [hζw]; exact hw)
  have hnd : ringKrullDim (P.presheaf.stalk (a.hom.base ⟨ζ, hζdom⟩)) ≠ 0 := by
    intro h0
    apply hbd
    rw [eq_genericPoint_of_ringKrullDim_stalk_eq_zero p _ h0]
    obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
    exact ((genericPoint_spec P).mem_open_set_iff D.isOpen).mpr ⟨_, Set.mem_univ _, (ι.base v).2⟩
  obtain ⟨P'', p'', hP''i, hP''p, β, hβ, W, hWd, hβW, U', hU', hζU', α', hα', hα'ζ⟩ :=
    exists_isProper_isIso_morphismRestrict_ringKrullDim_stalk_eq_one_of_ringKrullDim_stalk_eq_one
      (pullback.fst f p ≫ f) p a.dom a.hom (by rw [a.hom_comp, pullback.condition]) hdomα ζ hζdom
        hζ₁ hζn hnd
  have : IsIntegral P'' := hP''i
  have : IsProper p'' := hP''p
  have : LocallyOfFiniteType p'' := inferInstance
  have : QuasiCompact p'' := inferInstance
  obtain ⟨P', ν, hP'i, hP'n, hνfin, hνsurj, hνdim, hνiso⟩ :=
    exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral k p''
  have : IsIntegral P' := hP'i
  have : IsFinite ν := hνfin
  refine ⟨P', ν ≫ β, ?_⟩
  have hβWn : IsIso (ν ∣_ (β ⁻¹ᵁ W)) := hνiso _ (fun y hy => by
    have : IsIso (β.stalkMap y) :=
      isIso_stalkMap_of_isIso_morphismRestrict
        β W y hy
    have : IsIntegrallyClosed (P.presheaf.stalk (β.base y)) := hn _
    exact IsIntegrallyClosed.of_equiv (asIso (β.stalkMap y)).commRingCatIsoToRingEquiv)
  have hπW : IsIso ((ν ≫ β) ∣_ W) := by
    rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hβWn hβW
  let ι₀ : (V : Scheme.{u}) ⟶ P := ι ≫ D.ι
  let V' : G.Opens := V.ι ''ᵁ (ι₀ ⁻¹ᵁ W)
  let ι' : (V' : Scheme.{u}) ⟶ P' :=
    (V.ι.isoImage (ι₀ ⁻¹ᵁ W)).inv ≫ (ι₀ ∣_ W) ≫ inv ((ν ≫ β) ∣_ W) ≫ ((ν ≫ β) ⁻¹ᵁ W).ι
  have hι'π : ι' ≫ (ν ≫ β) = (V.ι.isoImage (ι₀ ⁻¹ᵁ W)).inv ≫ (ι₀ ⁻¹ᵁ W).ι ≫ ι₀ := by
    simp only [ι', Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  have hι' : ι' ≫ (ν ≫ β) ≫ p = V'.ι ≫ f := by
    rw [← Category.assoc, hι'π, Category.assoc, Category.assoc, hι₀, ← Category.assoc ((ι₀ ⁻¹ᵁ
      W).ι),
      ← Category.assoc, Scheme.Hom.isoImage_inv_ι]
  have : IsOpenImmersion ι' := by
    simp only [ι']; infer_instance
  have : Nonempty (V' : Scheme.{u}) := by
    obtain ⟨x, ⟨v, rfl⟩, hxW⟩ := hWd.inter_open_nonempty _ ι₀.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    exact ⟨⟨V.ι.base v, (Scheme.Opens.mem_ι_image_iff V).mpr hxW⟩⟩
  have : IsProper β := isProper_of_comp_eq p'' p β hβ
  have : IsProper (ν ≫ β) := inferInstance
  have : IsProper ((ν ≫ β) ≫ p) := inferInstance
  obtain ⟨a', hc', hm', hcod'⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_partialAction_compatible_maximal_of_isProper k f
      L ((ν ≫ β) ≫ p)
      hP'n V' ι' hι'
  have : LocallyOfFiniteType p := inferInstance
  have : QuasiCompact p := inferInstance
  have hWne : (W : Set P).Nonempty := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (V : Scheme.{u}))
    exact hWd.nonempty_iff.mpr ⟨ι₀.base v⟩
  obtain ⟨w', hπw', hisow'⟩ :=
    AlgebraicGeometry.exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one p (ν
    ≫ β) W
    hWne w hw₁ (hn w)
  have hw'₁ : ringKrullDim (P'.presheaf.stalk w') = 1 := by
    rw [← hw₁, ← hπw']
    exact (ringKrullDim_eq_of_ringEquiv (asIso ((ν ≫ β).stalkMap
      w')).commRingCatIsoToRingEquiv).symm
  have : LocallyOfFiniteType ((ν ≫ β) ≫ p) := inferInstance
  obtain ⟨ζ', hζ'cl, hζ'w, hζ'dim⟩ :=
    AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat f ((ν ≫
      β) ≫ p) w'
  have hζ'dom : ζ' ∈ a'.dom := hcod' ζ' (by rw [hζ'dim, hw'₁])
  let w'' : P' := a'.hom.base ⟨ζ', hζ'dom⟩
  have hV'V : V' ≤ V := Scheme.Opens.ι_image_le _ _
  have hV'W : Set.range (G.homOfLE hV'V ≫ ι₀).base ⊆ (W : Set P) := by
    rintro _ ⟨x, rfl⟩
    change ι₀.base ((G.homOfLE hV'V).base x) ∈ (W : Set P)
    have hx : V.ι ((G.homOfLE hV'V).base x) ∈ (V' : Set G) := by
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact x.2
    have : (G.homOfLE hV'V).base x ∈ ι₀ ⁻¹ᵁ W := (Scheme.Opens.mem_ι_image_iff V).mp hx
    exact this
  have hι'ι₀ : ι' ≫ ν ≫ β = G.homOfLE hV'V ≫ ι₀ := by
    rw [hι'π, ← Category.assoc]
    congr 1
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι]
    exact (Scheme.Hom.isoImage_inv_ι V.ι (ι₀ ⁻¹ᵁ W))
  have : IsSeparated p'' := inferInstance
  have hνw'' : ν.base w'' = α'.base ⟨ζ, hζU'⟩ :=
    GoodReductionJacobian.PartialAction.base_hom_eq_of_compatible_of_isIso_stalkMap k f L p V ι₀
      hι₀ a hc w ζ hζdom
      hζcl p'' β hβ W U' hU' hζU' α' hα' ν V' hV'V hV'W ι' hι'ι₀ hι' a' hc' w' hπw' hisow' ζ'
        hζ'dom hζ'cl
  have hw''₁ : ringKrullDim (P'.presheaf.stalk w'') = 1 := by rw [hνdim, hνw'', hα'ζ]
  have hsweep : closure (a'.hom.base '' ((a'.dom.ι ≫ pullback.snd f ((ν ≫ β) ≫ p)).base ⁻¹'
    closure {w'})) =
      closure {w''} :=
    GoodReductionJacobian.PartialAction.closure_image_preimage_closure_eq_closure_singleton a'
      {w'} ζ' hζ'dom hζ'cl
  have : LocallyOfFiniteType ((ν ≫ β) ≫ p) := inferInstance
  have hdimP' : topologicalKrullDim ↥P' = topologicalKrullDim ↥G := by
    have h1 := AlgebraicGeometry.topologicalKrullDim_eq_of_iso_opens ((ν ≫ β) ≫ p) p ((ν ≫ β) ⁻¹ᵁ
      W) W
      (by obtain ⟨y, hy⟩ := hWne
          exact ⟨((inv ((ν ≫ β) ∣_ W)).base ⟨y, hy⟩).1, ((inv ((ν ≫ β) ∣_ W)).base ⟨y, hy⟩).2⟩)
      (asIso ((ν ≫ β) ∣_ W))
    have : IrreducibleSpace G := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
    have : IsIntegral G := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
    have h2 := AlgebraicGeometry.topologicalKrullDim_eq_of_iso_opens f p V ι₀.opensRange
      ((Scheme.Opens.nonempty_iff _).mp inferInstance) ι₀.isoOpensRange
    exact h1.trans h2.symm
  exact ⟨V', ι', hι', a', w', w'', hP'i, hP'n, inferInstance, hdimP', inferInstance,
    inferInstance, hc', hm', hcod',
    hπw', hw'₁, hw''₁, hsweep⟩

end GoodReductionJacobian.PartialAction
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.StableLocus

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open Topology

namespace GoodModel
open _root_.GoodReductionJacobian.PartialAction
open _root_.GoodReductionJacobian

section Assembly

theorem exists_model (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f] (hG : ¬ IsProper f) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k)) (V : G.Opens)
      (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f) (a : PartialAction k f p)
      (W : Set ↥P) (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p),
      IsProper p ∧ IsIntegral P ∧ (∀ x : P, IsIntegrallyClosed (P.presheaf.stalk x)) ∧
      Nonempty (V : Scheme.{u}) ∧ IsOpenImmersion ι ∧
      a.Compatible L V ι hι ∧ a.Maximal ∧
      (∀ z : ↥(pullback f p), ringKrullDim ((pullback f p).presheaf.stalk z) ≤ 1 → z ∈ a.dom) ∧
      IsClosed W ∧ topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞) ∧ a.Stable W ∧
      P₀.1 (fieldPoint k) ∈ W ∧
      a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : IsIntegral G := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
  have : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have hnG : ∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x) := fun x =>
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk f x).2
  obtain ⟨P₁, p₁, D₁, τ₁, V₁, ι₁, hp₁, hP₁, hn₁, hτ₁, hτ₁f, hV₁, hι₁, hτι₁⟩ :=
    exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
      k f hnG
  have : IsProper p₁ := hp₁
  have : IsIntegral P₁ := hP₁
  have : IsProper τ₁ := hτ₁
  have : Nonempty (V₁ : Scheme.{u}) := hV₁
  have : IsOpenImmersion ι₁ := hι₁
  obtain ⟨P₂, π, V₂, ι₂, hP₂, hn₂, hπ, hV₂, hι₂, hτι₂, w₂, hw₂, hw₂₁⟩ :=
    AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
      k f hG p₁ hn₁ D₁ τ₁ hτ₁f V₁ ι₁ hτι₁
  have : IsIntegral P₂ := hP₂
  have : IsProper π := hπ
  have : Nonempty (V₂ : Scheme.{u}) := hV₂
  have : IsOpenImmersion ι₂ := hι₂
  have hp₂ : IsProper (π ≫ p₁) := inferInstance
  have hτ₂ : IsProper ((π ∣_ D₁) ≫ τ₁) := inferInstance
  have hτ₂f : ((π ∣_ D₁) ≫ τ₁) ≫ f = (π ⁻¹ᵁ D₁).ι ≫ π ≫ p₁ := by
    rw [Category.assoc, hτ₁f, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hτι₂' : ι₂ ≫ ((π ∣_ D₁) ≫ τ₁) = V₂.ι := by rw [hτι₂]
  obtain ⟨P₃, π₃, V₃, ι₃, hι₃, a₃, w₃, w₃', hP₃, hn₃, hπ₃, hdim₃, hV₃, hι₃o, hc₃, hm₃, hcod₃, -,
      hw₃₁, hw₃'₁, hsw⟩ :=
    exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one
      k f L (π ≫ p₁) hn₂ (π ⁻¹ᵁ D₁) ((π ∣_ D₁) ≫ τ₁) hτ₂f V₂ ι₂ hτι₂' w₂ hw₂ hw₂₁
  have : IsIntegral P₃ := hP₃
  have : IsProper π₃ := hπ₃
  have : Nonempty (V₃ : Scheme.{u}) := hV₃
  have : IsOpenImmersion ι₃ := hι₃o
  have hp₃ : IsProper (π₃ ≫ π ≫ p₁) := inferInstance
  obtain ⟨hu, ha⟩ :=
    GoodReductionJacobian.PartialAction.unitActs_and_assoc_of_compatible_of_maximal
      k f L (π₃ ≫ π ≫ p₁) V₃ ι₃ hι₃ a₃ hc₃ hm₃
  obtain ⟨P₀, hdimW, hst, hP₀, he⟩ :=
    exists_stable_defined_one_of_closure_image_eq_closure_singleton
      k f L (π₃ ≫ π ≫ p₁) a₃ hu ha hcod₃ w₃ w₃' hw₃₁ hw₃'₁ hsw
  have : Nonempty G := ⟨(L.one (𝟙 _)).1.base (fieldPoint k)⟩
  have hdimG : topologicalKrullDim G = g :=
    le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le f g)
      (SmoothOfRelativeDimension.le_topologicalKrullDim f g)
  rw [hdim₃, hdimG] at hdimW
  exact ⟨P₃, π₃ ≫ π ≫ p₁, V₃, ι₃, hι₃, a₃, closure {w₃'}, P₀, hp₃, hP₃, hn₃, hV₃, hι₃o, hc₃, hm₃,
    hcod₃, isClosed_closure, hdimW, hst, hP₀, he⟩

end Assembly

end GoodModel

end AbelianVarieties.NOSProofs.StableLocus

namespace GoodReductionJacobian.PartialAction

theorem
    exists_compatible_stable_defined_one_of_not_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f] (hG : ¬ IsProper f) :
    ∃ (V : G.Opens) (_ : Nonempty (V : Scheme.{u})) (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of
      k))
      (_ : IsSeparated p) (_ : LocallyOfFiniteType p) (_ : IsIntegral P)
      (ι : (V : Scheme.{u}) ⟶ P) (_ : IsOpenImmersion ι) (hι : ι ≫ p = V.ι ≫ f)
      (a : PartialAction k f p), a.Compatible L V ι hι ∧ a.UnitActs L ∧ a.Assoc L ∧
      ∃ (W : Set ↥P), IsClosed W ∧ a.Stable W ∧ topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞) ∧
        ∃ P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
          P₀.1 (IsLocalRing.closedPoint k) ∈ W ∧ a.Defined (L.one (𝟙 (Spec (CommRingCat.of k))))
            P₀ := by
  obtain ⟨P, p, V, ι, hι, a, W, P₀, hp, hP, -, hV, hιo, hc, hm, -, hW, hdim, hst, hP₀, he⟩ :=
    AbelianVarieties.NOSProofs.StableLocus.GoodModel.exists_model k f L g hG
  have : IsProper p := hp
  have : Nonempty (V : Scheme.{u}) := hV
  have : IsOpenImmersion ι := hιo
  have : IsIntegral P := hP
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  obtain ⟨hu, ha⟩ :=
    GoodReductionJacobian.PartialAction.unitActs_and_assoc_of_compatible_of_maximal
      k f L p V ι hι a hc hm
  exact ⟨V, hV, P, p, inferInstance, inferInstance, hP, ι, hιo, hι, a, hc, hu, ha, W, hW, hst, hdim,
    P₀, hP₀, he⟩

end GoodReductionJacobian.PartialAction
end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Pi1.GaloisCategories.TrivialMonodromy
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Surjectivity
public import Nyll.EtaleFundamentalGroups.GaloisCategories.PointStabilizerMorphism
public import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# The fundamental group of a trivial-monodromy Galois category

Restriction to the actual objects on which a closed normal subgroup `N` acts
trivially is surjective on fibre-functor automorphisms and has kernel exactly
`N`. To detect the kernel, every open normal subgroup containing `N` is
realized by a pointed Galois object in the original category. Thus the
restricted fibre functor has fundamental group canonically `Aut F / N`,
with the comparison retaining the original automorphism representatives.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (N : Subgroup (Aut F))

/-- Restrict the original fibre-functor automorphism to the actual full subcategory. -/
def trivialMonodromyRestriction : Aut F →ₜ* Aut (trivialMonodromyFiber F N) :=
  autHomOfCompIso (trivialMonodromyInclusion F N) (Iso.refl _)

omit [GaloisCategory C] [FiberFunctor F] in
/-- Restriction evaluates the original automorphism on the original fibre. -/
@[simp] theorem trivialMonodromyRestriction_apply
    (g : Aut F) (X : TrivialMonodromy F N) (x : F.obj X.obj) :
    (trivialMonodromyRestriction F N g).asIso.hom.app X x =
      g.asIso.hom.app X.obj x := rfl

/-- Full faithfulness of the actual inclusion makes restriction surjective. -/
theorem trivialMonodromyRestriction_surjective :
    Function.Surjective (trivialMonodromyRestriction F N) := by
  have hff : Nonempty (trivialMonodromyInclusion F N).FullyFaithful :=
    ⟨(trivialMonodromy F N).fullyFaithfulι⟩
  exact ((autHomOfCompIso_surjective_tfae (trivialMonodromyFiber F N) F
    (trivialMonodromyInclusion F N) (Iso.refl _)).out 2 1).mp hff

omit [GaloisCategory C] [FiberFunctor F] in
/-- Every element of the prescribed subgroup acts trivially after restriction. -/
theorem le_ker_trivialMonodromyRestriction :
    N ≤ (trivialMonodromyRestriction F N).toMonoidHom.ker := by
  intro g hg
  change trivialMonodromyRestriction F N g = 1
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply FintypeCat.hom_ext
  intro x
  exact (trivialMonodromy_iff F N X.obj).mp X.property g hg x

variable [N.Normal] (hN : IsClosed (N : Set (Aut F)))

include hN in
/-- Finite Galois objects detect every element outside the closed normal subgroup. -/
theorem trivialMonodromyRestriction_ker :
    (trivialMonodromyRestriction F N).toMonoidHom.ker = N := by
  apply le_antisymm ?_ (le_ker_trivialMonodromyRestriction F N)
  intro g hg
  let K : ClosedSubgroup (Aut F) := ⟨N, hN⟩
  change g ∈ (K : Subgroup (Aut F))
  rw [ProCGroups.ProC.closedSubgroup_eq_sInf_openNormal K]
  simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
  intro U hU
  let V : OpenNormalSubgroup (Aut F) :=
    { toSubgroup := U
      isOpen' := hU.1
      isNormal' := hU.2.2 }
  obtain ⟨A, hA, x, hx⟩ := exists_galois_object_point_stabilizer_eq_any_universe F V
  have : IsGalois A := hA
  have hAN : trivialMonodromy F N A := by
    apply (trivialMonodromy_iff F N A).mpr
    intro n hn y
    change n ∈ MulAction.stabilizer (Aut F) y
    rw [← stabilizer_eq_of_isGalois F A x y, hx]
    exact hU.2.1 hn
  let B : TrivialMonodromy F N := ⟨A, hAN⟩
  have hfix : (trivialMonodromyRestriction F N g).asIso.hom.app B x = x := by
    rw [show trivialMonodromyRestriction F N g = 1 from hg]
    rfl
  rw [trivialMonodromyRestriction_apply] at hfix
  have hstab : g ∈ MulAction.stabilizer (Aut F) x := hfix
  rw [hx] at hstab
  exact hstab

/-- The restriction map descended through the prescribed closed normal subgroup. -/
def trivialMonodromyQuotientMap :
    Aut F ⧸ N →ₜ* Aut (trivialMonodromyFiber F N) :=
  ProCGroups.QuotientGroup.liftₜ N (trivialMonodromyRestriction F N)
    (le_ker_trivialMonodromyRestriction F N)

omit [GaloisCategory C] [FiberFunctor F] in
/-- The descended restriction map retains each original automorphism. -/
@[simp] theorem trivialMonodromyQuotientMap_apply_mk (g : Aut F) :
    trivialMonodromyQuotientMap F N (QuotientGroup.mk' N g) =
      trivialMonodromyRestriction F N g := rfl

include hN in
/-- The quotient restriction map is bijective by its exact original kernel. -/
theorem trivialMonodromyQuotientMap_bijective :
    Function.Bijective (trivialMonodromyQuotientMap F N) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff
      (trivialMonodromyQuotientMap F N).toMonoidHom).mp
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro a ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N a
    apply (QuotientGroup.eq_one_iff (N := N) g).mpr
    rw [← trivialMonodromyRestriction_ker F N hN]
    exact ha
  · intro a
    obtain ⟨g, rfl⟩ := trivialMonodromyRestriction_surjective F N a
    exact ⟨QuotientGroup.mk' N g, rfl⟩

/-- The automorphism group of the restricted fibre functor is canonically the
quotient of the original group; the inverse gives the opposite comparison. -/
def trivialMonodromyQuotientEquiv :
    Aut F ⧸ N ≃ₜ* Aut (trivialMonodromyFiber F N) :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (trivialMonodromyQuotientMap F N).toMonoidHom
    (trivialMonodromyQuotientMap F N).continuous_toFun
    (trivialMonodromyQuotientMap_bijective F N hN)

/-- The comparison identifies the quotient projection with actual restriction. -/
@[simp] theorem trivialMonodromyQuotientEquiv_apply_mk (g : Aut F) :
    trivialMonodromyQuotientEquiv F N hN (QuotientGroup.mk' N g) =
      trivialMonodromyRestriction F N g := rfl

/-- The inverse comparison sends a restricted automorphism to its original quotient class. -/
@[simp] theorem trivialMonodromyQuotientEquiv_symm_apply_restriction (g : Aut F) :
    (trivialMonodromyQuotientEquiv F N hN).symm
        (trivialMonodromyRestriction F N g) = QuotientGroup.mk' N g := by
  rw [← trivialMonodromyQuotientEquiv_apply_mk F N hN g]
  exact (trivialMonodromyQuotientEquiv F N hN).symm_apply_apply _

end CategoryTheory.PreGaloisCategory
